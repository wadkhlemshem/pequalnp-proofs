import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CircuitMoves

section Fold

variable {α : Type} (f : List α → Gate → List α)
  (hf : ∀ R g, (f R g).take R.length = R) (hl : ∀ R g, (f R g).length = R.length + 1)
include hf hl

theorem fl_length (gs : List Gate) (init : List α) :
    (gs.foldl f init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, hl]; simp; omega

theorem fl_take (gs : List Gate) (init : List α) :
    (gs.foldl f init).take init.length = init := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have e := ih (f init g)
    rw [hl] at e
    have : (gs.foldl f (f init g)).take init.length =
        ((gs.foldl f (f init g)).take (init.length + 1)).take init.length := by
      rw [List.take_take]; simp
    rw [this, e, hf]

theorem fl_take_succ (gs : List Gate) (init : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl f init).take (init.length + j + 1) =
      f ((gs.foldl f init).take (init.length + j)) gs[j] := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have e := fl_take f hf hl gs (f init g)
      rw [hl] at e
      have e2 : (gs.foldl f (f init g)).take init.length = init := by
        have : (gs.foldl f (f init g)).take init.length =
            ((gs.foldl f (f init g)).take (init.length + 1)).take init.length := by
          rw [List.take_take]; simp
        rw [this, e, hf]
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [e, e2]
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have e := ih (f init g) j hj'
      rw [hl] at e
      simp only [List.getElem_cons_succ]
      have h1 : init.length + (j + 1) + 1 = init.length + 1 + j + 1 := by omega
      have h2 : init.length + (j + 1) = init.length + 1 + j := by omega
      rw [h1, h2, e]

theorem fl_get (gs : List Gate) (init : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl f init)[init.length + j]? =
      (f ((gs.foldl f init).take (init.length + j)) gs[j])[init.length + j]? := by
  rw [← fl_take_succ f hf hl gs init j hj, List.getElem?_take]
  simp

theorem fl_init (gs : List Gate) (init : List α) (i : ℕ) (hi : i < init.length) :
    (gs.foldl f init)[i]? = init[i]? := by
  conv_rhs => rw [← fl_take f hf hl gs init]
  rw [List.getElem?_take]; simp [hi]

end Fold

theorem take_getD {β : Type} (L : List β) (m i : ℕ) (d : β) (hi : i < m) :
    (L.take m).getD i d = L.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

section Wires

def wf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wf_take (R : List Bool) (g : Gate) : (wf R g).take R.length = R := by simp [wf]
theorem wf_len (R : List Bool) (g : Gate) : (wf R g).length = R.length + 1 := by simp [wf]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wf x := rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq, List.getD_eq_getElem?_getD, fl_init wf wf_take wf_len _ _ i hi,
    ← List.getD_eq_getElem?_getD]

theorem wires_gate (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq, List.getD_eq_getElem?_getD]
  have e := fl_get wf wf_take wf_len C.gates x j hj
  rw [hx] at e
  rw [e]
  have hlen : ((C.gates.foldl wf x).take (n + j)).length = n + j := by
    rw [List.length_take, fl_length wf wf_take wf_len, hx]; omega
  simp only [wf]
  rw [List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hr := hb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  exact take_getD _ _ _ _ hr

end Wires

section Lift

theorem wires_gate' (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    (C.wires x).getD (n + j) false = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  exact wires_gate n C hb x hx j hj

theorem rb' (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  intro i hi
  exact hb j hj i (by rw [gateAt_eq C j hj]; exact hi)

theorem mem_of_get? (l : List Gate) (j : ℕ) (g : Gate) (hg : l[j]? = some g) : g ∈ l := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  exact List.getElem_mem hj

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (v1 v2 : ℕ → Bool) (h : ∀ i ∈ l, v1 i = true → v2 i = true)
    (he : op.eval (l.map v1) = true) : op.eval (l.map v2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at he ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact h i hi (he _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at he ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := he
    exact ⟨_, ⟨i, hi, rfl⟩, h i hi hv⟩

theorem eval_hi (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (v v' : ℕ → Bool) (b : Bool) (h : ∀ i ∈ l, v i = true → v' i = true ∨ b = true)
    (he : op.eval (l.map v) = true) : op.eval (l.map v') = true ∨ b = true := by
  by_cases hb : b = true
  · exact Or.inr hb
  · exact Or.inl (eval_mono op hop l v v' (fun i hi hv => (h i hi hv).resolve_right hb) he)

def newGates (n m p h : ℕ) (C : Circuit) : List Gate :=
  C.gates.take m ++
    (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) ++
    [⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩]

theorem ng_len (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) :
    (newGates n m p h C).length = C.gates.length := by
  simp only [newGates, List.length_append, List.length_take, List.length_map, List.length_drop,
    List.length_cons, List.length_nil]
  omega

theorem liftAt_eq (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) :
    liftAt n C m p h = ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ := by
  unfold liftAt eraseGate newGates
  simp only [if_pos hm]
  refine congrArg₂ Circuit.mk rfl ?_
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem ng_lt (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) (j : ℕ) (hj : j < m) :
    (newGates n m p h C)[j]? = C.gates[j]? := by
  unfold newGates
  rw [List.append_assoc, List.getElem?_append_left (by rw [List.length_take]; omega),
    List.getElem?_take]
  simp [hj]

theorem ng_mid (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) (j : ℕ) (hmj : m ≤ j)
    (hj : j + 1 < C.gates.length) :
    (newGates n m p h C)[j]? =
      (C.gates[j + 1]?).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
  have e : (List.take m C.gates).length = m := by rw [List.length_take]; omega
  unfold newGates
  rw [List.append_assoc, List.getElem?_append_right (by rw [e]; exact hmj),
    List.getElem?_append_left (by rw [e, List.length_map, List.length_drop]; omega),
    e, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem ng_last (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) :
    (newGates n m p h C)[C.gates.length - 1]? =
      some ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ := by
  have e : (C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).length
      = C.gates.length - 1 := by
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  unfold newGates
  rw [List.getElem?_append_right (by rw [e]), e, Nat.sub_self]
  rfl

theorem ng_cases (n m p h : ℕ) (C : Circuit) (hm : m < C.gates.length) (j : ℕ) (g : Gate)
    (hjg : (newGates n m p h C)[j]? = some g) :
    (j < m ∧ C.gates[j]? = some g) ∨
    (m ≤ j ∧ j + 1 < C.gates.length ∧ ∃ g0, C.gates[j + 1]? = some g0 ∧
      g = ⟨g0.op, g0.inputs.map (eraseRedirect n m p)⟩) ∨
    (j + 1 = C.gates.length ∧ g = ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩) := by
  have hj : j < C.gates.length := by
    have h0 := (List.getElem?_eq_some_iff.mp hjg).1
    rw [ng_len n m p h C hm] at h0; exact h0
  by_cases h1 : j < m
  · left; exact ⟨h1, by rw [← ng_lt n m p h C hm j h1]; exact hjg⟩
  by_cases h2 : j + 1 < C.gates.length
  · right; left
    refine ⟨by omega, h2, ?_⟩
    rw [ng_mid n m p h C hm j (by omega) h2] at hjg
    obtain ⟨g0, hg0, hfg⟩ := Option.map_eq_some_iff.mp hjg
    exact ⟨g0, hg0, hfg.symm⟩
  · right; right
    have hjl : j = C.gates.length - 1 := by omega
    rw [hjl, ng_last n m p h C hm] at hjg
    exact ⟨by omega, (Option.some.inj hjg).symm⟩

theorem rho_lt (n m p j i : ℕ) (hi : i < n + j + 1) (hmj : m ≤ j) (hp : p < n + m) :
    eraseRedirect n m p i < n + j := by
  unfold eraseRedirect
  split_ifs <;> omega

theorem rb1 (n m p h : ℕ) (C : Circuit) (hb : ReadsBack n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m) (ho : C.output < n + C.gates.length) :
    ReadsBack n ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ := by
  intro j hj i hi
  rw [gateAt_eq _ j hj] at hi
  have hg : (newGates n m p h C)[j]? = some ((newGates n m p h C)[j]'hj) :=
    List.getElem?_eq_getElem hj
  rcases ng_cases n m p h C hm j _ hg with ⟨h1, hg0⟩ | ⟨h1, h2, g0, hg0, hgg⟩ | ⟨h1, hgg⟩
  · exact rb' n C hb j _ hg0 i hi
  · have hi' : i ∈ (⟨g0.op, g0.inputs.map (eraseRedirect n m p)⟩ : Gate).inputs := hgg ▸ hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi'
    exact rho_lt n m p j i0 (rb' n C hb (j + 1) g0 hg0 i0 hi0) h1 hp
  · have hi' : i ∈ (⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ : Gate).inputs := hgg ▸ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl
    · exact rho_lt n m p j C.output (by omega) (by omega) hp
    · omega

theorem ao1 (n m p h : ℕ) (C : Circuit) (hA : AndOrOnly C) (hm : m < C.gates.length) :
    AndOrOnly ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ := by
  intro g hg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
  rcases ng_cases n m p h C hm j g hj with ⟨_, hg0⟩ | ⟨_, _, g0, hg0, rfl⟩ | ⟨_, rfl⟩
  · exact hA g (mem_of_get? _ j g hg0)
  · exact hA g0 (mem_of_get? _ _ g0 hg0)
  · exact Or.inr rfl

theorem val_m (n m p h : ℕ) (C : Circuit) (hb : ReadsBack n C)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    (C.wires x).getD (n + m) false =
      ((C.wires x).getD p false || (C.wires x).getD h false) := by
  rcases hg with hg | hg
  · rw [wires_gate' n C hb x hx m _ hg]; simp [GateOp.eval]
  · rw [wires_gate' n C hb x hx m _ hg]; simp [GateOp.eval, Bool.or_comm]

theorem valE (n m p h : ℕ) (C : Circuit) (hb : ReadsBack n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m) (ho : C.output < n + C.gates.length)
    (x : List Bool) (hx : x.length = n) :
    ∀ i, i < n + m →
      ((⟨newGates n m p h C, n + (C.gates.length - 1)⟩ : Circuit).wires x).getD i false =
        (C.wires x).getD i false := by
  have hb1 := rb1 n m p h C hb hm hp hh ho
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  by_cases hin : i < n
  · rw [wires_input _ x i (by omega), wires_input _ x i (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
  have hk : k < m := by omega
  obtain ⟨g, hg⟩ : ∃ g, C.gates[k]? = some g :=
    ⟨C.gates[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hg1 : (newGates n m p h C)[k]? = some g := by rw [ng_lt n m p h C hm k hk]; exact hg
  rw [wires_gate' n _ hb1 x hx k g hg1, wires_gate' n C hb x hx k g hg]
  congr 1
  apply List.map_congr_left
  intro i' hi'
  have hlt := rb' n C hb k g hg i' hi'
  exact ih i' hlt (by omega)

theorem valI (n m p h : ℕ) (C : Circuit) (hA : AndOrOnly C) (hb : ReadsBack n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (ho : C.output < n + C.gates.length) (x : List Bool) (hx : x.length = n) :
    ∀ i, i < n + C.gates.length →
      (((⟨newGates n m p h C, n + (C.gates.length - 1)⟩ : Circuit).wires x).getD
          (eraseRedirect n m p i) false = true → (C.wires x).getD i false = true) ∧
      ((C.wires x).getD i false = true →
        ((⟨newGates n m p h C, n + (C.gates.length - 1)⟩ : Circuit).wires x).getD
          (eraseRedirect n m p i) false = true ∨ (C.wires x).getD h false = true) := by
  have hb1 := rb1 n m p h C hb hm hp hh ho
  have hE := valE n m p h C hb hm hp hh ho x hx
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  by_cases h1 : i < n + m
  · have e : eraseRedirect n m p i = i := by
      unfold eraseRedirect; rw [if_neg (by omega), if_neg (by omega)]
    rw [e, hE i h1]; exact ⟨id, Or.inl⟩
  by_cases h2 : i = n + m
  · have e : eraseRedirect n m p i = p := by
      unfold eraseRedirect; rw [if_pos h2]
    rw [e, hE p hp, h2, val_m n m p h C hb hg x hx]
    constructor
    · intro hpv; rw [hpv]; rfl
    · intro hor
      exact Bool.or_eq_true _ _ ▸ hor
  obtain ⟨j, rfl⟩ : ∃ j, i = n + (j + 1) := ⟨i - n - 1, by omega⟩
  have hmj : m ≤ j := by omega
  have hj : j + 1 < C.gates.length := by omega
  have e : eraseRedirect n m p (n + (j + 1)) = n + j := by
    unfold eraseRedirect; rw [if_neg (by omega), if_pos (by omega)]; omega
  obtain ⟨g, hg0⟩ : ∃ g, C.gates[j + 1]? = some g := ⟨_, List.getElem?_eq_getElem hj⟩
  have hg1 : (newGates n m p h C)[j]? =
      some ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ := by
    rw [ng_mid n m p h C hm j hmj hj, hg0]; rfl
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := hA g (mem_of_get? _ _ g hg0)
  have hlt := rb' n C hb (j + 1) g hg0
  rw [e, wires_gate' n _ hb1 x hx j _ hg1, wires_gate' n C hb x hx (j + 1) g hg0]
  simp only [List.map_map]
  constructor
  · exact eval_mono g.op hop g.inputs _ _ (fun i' hi' hv =>
      (ih i' (hlt i' hi') (by have := hlt i' hi'; omega)).1 hv)
  · exact eval_hi g.op hop g.inputs _ _ _ (fun i' hi' hv =>
      (ih i' (hlt i' hi') (by have := hlt i' hi'; omega)).2 hv)

theorem eval_lift (n m p h : ℕ) (C : Circuit) (hA : AndOrOnly C) (hb : ReadsBack n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (ho : C.output < n + C.gates.length) (hw : WireBelowOutput n C h) (x : Fin n → Bool) :
    (⟨newGates n m p h C, n + (C.gates.length - 1)⟩ : Circuit).eval (List.ofFn x) =
      C.eval (List.ofFn x) := by
  have hb1 := rb1 n m p h C hb hm hp hh ho
  have hx : (List.ofFn x).length = n := by simp
  have hI := valI n m p h C hA hb hm hp hh hg ho (List.ofFn x) hx C.output ho
  have hE := valE n m p h C hb hm hp hh ho (List.ofFn x) hx h hh
  have hwx := hw x
  unfold Circuit.eval at hwx ⊢
  rw [wires_gate' n _ hb1 (List.ofFn x) hx (C.gates.length - 1) _ (ng_last n m p h C hm)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id]
  rw [hE, Bool.eq_iff_iff, Bool.or_eq_true]
  constructor
  · rintro (h1 | h2)
    · exact hI.1 h1
    · exact hwx h2
  · intro h3
    exact hI.2 h3

def mu (n : ℕ) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => ¬ WireBelowOutput n C (n + j))).card

theorem mu_lt (n m p h : ℕ) (C : Circuit) (hA : AndOrOnly C) (hb : ReadsBack n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (ho : C.output < n + C.gates.length) (hw : WireBelowOutput n C h)
    (hnp : ¬ WireBelowOutput n C p) :
    mu n ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ < mu n C := by
  have hev := eval_lift n m p h C hA hb hm hp hh hg ho hw
  have hinj : Function.Injective (fun j : ℕ => if j < m then j else j + 1) := by
    intro a b hab
    simp only at hab
    split_ifs at hab <;> omega
  have hm0 : m ∈ (Finset.range C.gates.length).filter
      (fun j => ¬ WireBelowOutput n C (n + j)) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hm, fun hW => hnp (fun x hv => hW x ?_)⟩
    rw [val_m n m p h C hb hg (List.ofFn x) (by simp), hv]; rfl
  have hsub : ((Finset.range (newGates n m p h C).length).filter
      (fun j => ¬ WireBelowOutput n ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ (n + j))).image
        (fun j : ℕ => if j < m then j else j + 1) ⊆
      ((Finset.range C.gates.length).filter
        (fun j => ¬ WireBelowOutput n C (n + j))).erase m := by
    intro k hk
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_filter, Finset.mem_range, ng_len n m p h C hm] at hj'
    obtain ⟨hjl, hnW⟩ := hj'
    have hne : j' + 1 ≠ C.gates.length := by
      intro he
      apply hnW
      have : n + j' = n + (C.gates.length - 1) := by omega
      rw [this]
      intro x hv
      exact hv
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · show (if j' < m then j' else j' + 1) ≠ m
      split_ifs <;> omega
    · show (if j' < m then j' else j' + 1) < C.gates.length
      split_ifs <;> omega
    · intro hW
      apply hnW
      intro x hv
      rw [hev x]
      apply hW x
      have hx : (List.ofFn x).length = n := by simp
      show (C.wires (List.ofFn x)).getD (n + (if j' < m then j' else j' + 1)) false = true
      split_ifs with hlt
      · rw [← valE n m p h C hb hm hp hh ho (List.ofFn x) hx (n + j') (by omega)]
        exact hv
      · have hI := valI n m p h C hA hb hm hp hh hg ho (List.ofFn x) hx (n + (j' + 1)) (by omega)
        have e : eraseRedirect n m p (n + (j' + 1)) = n + j' := by
          unfold eraseRedirect; rw [if_neg (by omega), if_pos (by omega)]; omega
        rw [e] at hI
        exact hI.1 hv
  calc mu n ⟨newGates n m p h C, n + (C.gates.length - 1)⟩
      = (((Finset.range (newGates n m p h C).length).filter
          (fun j => ¬ WireBelowOutput n ⟨newGates n m p h C, n + (C.gates.length - 1)⟩ (n + j))).image
            (fun j : ℕ => if j < m then j else j + 1)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (((Finset.range C.gates.length).filter
          (fun j => ¬ WireBelowOutput n C (n + j))).erase m).card := Finset.card_le_card hsub
    _ < mu n C := Finset.card_erase_lt_of_mem hm0

theorem step (n m p h : ℕ) (C : Circuit) (hA : AndOrOnly C) (hb : ReadsBack n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m) (hnh : n ≤ h)
    (hg : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (ho : C.output < n + C.gates.length) (hw : WireBelowOutput n C h)
    (hnp : ¬ WireBelowOutput n C p) :
    ∃ C1 : Circuit, Lift n C C1 ∧ AndOrOnly C1 ∧ ReadsBack n C1 ∧
      C1.output < n + C1.gates.length ∧ mu n C1 < mu n C := by
  refine ⟨liftAt n C m p h, ⟨m, hm, p, hp, h, hh, hnh, hg, hw, rfl⟩, ?_⟩
  rw [liftAt_eq n m p h C hm]
  refine ⟨ao1 n m p h C hA hm, rb1 n m p h C hb hm hp hh ho, ?_,
    mu_lt n m p h C hA hb hm hp hh hg ho hw hnp⟩
  show n + (C.gates.length - 1) < n + (newGates n m p h C).length
  rw [ng_len n m p h C hm]; omega

theorem main (n : ℕ) : ∀ (k : ℕ) (C : Circuit), AndOrOnly C → ReadsBack n C →
    C.output < n + C.gates.length → mu n C ≤ k →
    ∃ C' : Circuit, Relation.ReflTransGen (Lift n) C C' ∧
      ∀ x6 < C'.gates.length, ∀ (x8 x9 : ℕ),
        C'.gates[x6]? = some ⟨GateOp.or, [x8, x9]⟩ →
        (n ≤ x9 → WireBelowOutput n C' x9 → WireBelowOutput n C' x8) ∧
        (n ≤ x8 → WireBelowOutput n C' x8 → WireBelowOutput n C' x9) := by
  intro k
  induction k with
  | zero =>
    intro C hA hb ho hmu
    refine ⟨C, Relation.ReflTransGen.refl, ?_⟩
    intro j hj a b hgate
    have ha : a < n + j := rb' n C hb j _ hgate a (by simp)
    have hbb : b < n + j := rb' n C hb j _ hgate b (by simp)
    constructor
    · intro hnb hWb
      by_contra hnWa
      obtain ⟨C1, _, _, _, _, hlt⟩ := step n j a b C hA hb hj ha hbb hnb (Or.inl hgate) ho hWb hnWa
      omega
    · intro hna hWa
      by_contra hnWb
      obtain ⟨C1, _, _, _, _, hlt⟩ := step n j b a C hA hb hj hbb ha hna (Or.inr hgate) ho hWa hnWb
      omega
  | succ k ih =>
    intro C hA hb ho hmu
    by_cases hgood : ∀ x6 < C.gates.length, ∀ (x8 x9 : ℕ),
        C.gates[x6]? = some ⟨GateOp.or, [x8, x9]⟩ →
        (n ≤ x9 → WireBelowOutput n C x9 → WireBelowOutput n C x8) ∧
        (n ≤ x8 → WireBelowOutput n C x8 → WireBelowOutput n C x9)
    · exact ⟨C, Relation.ReflTransGen.refl, hgood⟩
    · have hstep : ∃ C1 : Circuit, Lift n C C1 ∧ AndOrOnly C1 ∧ ReadsBack n C1 ∧
          C1.output < n + C1.gates.length ∧ mu n C1 < mu n C := by
        by_contra hno
        apply hgood
        intro j hj a b hgate
        have ha : a < n + j := rb' n C hb j _ hgate a (by simp)
        have hbb : b < n + j := rb' n C hb j _ hgate b (by simp)
        constructor
        · intro hnb hWb
          by_contra hnWa
          exact hno (step n j a b C hA hb hj ha hbb hnb (Or.inl hgate) ho hWb hnWa)
        · intro hna hWa
          by_contra hnWb
          exact hno (step n j b a C hA hb hj hbb ha hna (Or.inr hgate) ho hWa hnWb)
      obtain ⟨C1, hL, hA1, hb1, ho1, hlt⟩ := hstep
      obtain ⟨C', hreach, hC'⟩ := ih C1 hA1 hb1 ho1 (by omega)
      exact ⟨C', Relation.ReflTransGen.head hL hreach, hC'⟩

end Lift

end PEqualNP.Outside.L_meta_4295

open PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hC ho
  exact main n (mu n C) C hC.1 hC.2.1 ho le_rfl
