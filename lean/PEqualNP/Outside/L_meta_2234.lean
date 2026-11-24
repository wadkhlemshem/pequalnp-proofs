import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2234

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.ReadK PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

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

section OrSets

theorem os_take (n : ℕ) (R : List (List ℕ)) (g : Gate) : (orStep n R g).take R.length = R := by
  simp [orStep]
theorem os_len (n : ℕ) (R : List (List ℕ)) (g : Gate) :
    (orStep n R g).length = R.length + 1 := by simp [orStep]

theorem os_get (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (orSets n C).getD j [] = (orStep n ((orSets n C).take j) C.gates[j]).getD j [] := by
  have e := fl_get (orStep n) (os_take n) (os_len n) C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at e
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  exact congrArg (fun o => Option.getD o []) e

theorem os_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  have := fl_length (orStep n) (os_take n) (os_len n) C.gates []
  unfold orSets
  simpa using this

theorem os_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    j ∈ (orSets n C).getD j [] := by
  rw [os_get n C j hj]
  have hlen : ((orSets n C).take j).length = j := by
    rw [List.length_take, os_length]; omega
  unfold orStep
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

theorem os_step (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) (u : ℕ) (hu : u ∈ C.gates[j].inputs) (hnu : n ≤ u)
    (k : ℕ) (hk : k ∈ (orSets n C).getD (u - n) []) : k ∈ (orSets n C).getD j [] := by
  have hr := hb j hj u (by rw [gateAt_eq C j hj]; exact hu)
  rw [os_get n C j hj]
  have hlen : ((orSets n C).take j).length = j := by
    rw [List.length_take, os_length]; omega
  unfold orStep
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hor, ite_true,
    List.mem_cons]
  right
  rw [List.mem_flatMap]
  refine ⟨u, ?_, ?_⟩
  · rw [List.mem_filter]; exact ⟨hu, by simp [hnu, hr]⟩
  · rw [take_getD _ _ _ _ (by omega)]; exact hk

theorem os_cases (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j k : ℕ)
    (hk : k ∈ (orSets n C).getD j []) :
    j < C.gates.length ∧ (k = j ∨ (C.gates[j]'(by
      by_contra hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [os_length]; omega)] at hk
      simp at hk)).op = GateOp.or ∧
      ∃ u ∈ (C.gates[j]'(by
      by_contra hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [os_length]; omega)] at hk
      simp at hk)).inputs, n ≤ u ∧ u < n + j ∧ k ∈ (orSets n C).getD (u - n) []) := by
  have hj : j < C.gates.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [os_length]; omega)] at hk
    simp at hk
  refine ⟨hj, ?_⟩
  rw [os_get n C j hj] at hk
  have hlen : ((orSets n C).take j).length = j := by
    rw [List.length_take, os_length]; omega
  unfold orStep at hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)] at hk
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons] at hk
  rcases hk with hk | hk
  · exact Or.inl hk
  · right
    split_ifs at hk with hor
    · refine ⟨hor, ?_⟩
      rw [List.mem_flatMap] at hk
      obtain ⟨u, hu, hk⟩ := hk
      rw [List.mem_filter] at hu
      simp only [hlen, decide_eq_true_eq] at hu
      refine ⟨u, hu.1, hu.2.1, hu.2.2, ?_⟩
      rw [take_getD _ _ _ _ (by omega)] at hk
      exact hk
    · simp at hk

end OrSets

theorem reach_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  refine ⟨by omega, ?_⟩
  simpa using os_self n C j hj

theorem reach_lift (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) (u : ℕ) (hu : u ∈ C.gates[j].inputs) (k : ℕ)
    (hk : OrReaches n C u k) : OrReaches n C (n + j) k := by
  refine ⟨by omega, ?_⟩
  simpa using os_step n C hb j hj hor u hu hk.1 k hk.2

theorem orIn_lift (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hor : C.gates[j].op = GateOp.or) (u : ℕ) (hu : u ∈ C.gates[j].inputs) (i : Fin n)
    (hi : i ∈ orIn n C u) : i ∈ orIn n C (n + j) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  right
  rcases hi with hi | ⟨k, hk, hr, hko, hik⟩
  · refine ⟨j, hj, reach_self n C j hj, ?_, ?_⟩
    · rw [gateAt_eq C j hj]; exact hor
    · rw [gateAt_eq C j hj, hi]; exact hu
  · exact ⟨k, hk, reach_lift n C hb j hj hor u hu k hr, hko, hik⟩


section Semantics

theorem sem_reach (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (x : Fin n → Bool) :
    ∀ w k, OrReaches n C w k → (C.wires (List.ofFn x)).getD (n + k) false = true →
      (C.wires (List.ofFn x)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro k hr hk
  obtain ⟨hnw, hmem⟩ := hr
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnw
  rw [Nat.add_sub_cancel_left] at hmem
  obtain ⟨hj, hc⟩ := os_cases n C hb j k hmem
  rcases hc with hkj | ⟨hor, u, hu, hnu, hul, hku⟩
  · rw [← hkj]; exact hk
  · have hval := ih u (by omega) k ⟨hnu, hku⟩ hk
    rw [wires_gate n C hb _ (by simp) j hj, hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨_, ⟨u, hu, rfl⟩, hval⟩

theorem sem_orIn (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (i : Fin n) (w : ℕ)
    (h : i ∈ orIn n C w) :
    (C.wires (List.ofFn fun k => decide (k = i))).getD w false = true := by
  have hinp : (C.wires (List.ofFn fun k : Fin n => decide (k = i))).getD i.val false = true := by
    rw [wires_input C _ i.val (by simp)]
    simp [List.getD_eq_getElem?_getD]
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | ⟨k, hk, hr, hko, hik⟩
  · rw [← h]; exact hinp
  · apply sem_reach n C hb _ w k hr
    rw [wires_gate n C hb _ (by simp) k hk]
    rw [gateAt_eq C k hk] at hko hik
    rw [hko]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    exact ⟨_, ⟨i.val, hik, rfl⟩, hinp⟩

end Semantics

section Count

theorem os_le (n : ℕ) (C : Circuit) (hb : ReadsBack n C) :
    ∀ j k, k ∈ (orSets n C).getD j [] → j < C.gates.length ∧ k ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro k hk
  obtain ⟨hj, hc⟩ := os_cases n C hb j k hk
  refine ⟨hj, ?_⟩
  rcases hc with hkj | ⟨_, u, _, hnu, hul, hku⟩
  · omega
  · have := (ih (u - n) (by omega) k hku).2
    omega

theorem reach_bound (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (w k : ℕ)
    (h : OrReaches n C w k) : n ≤ w ∧ w - n < C.gates.length ∧ k ≤ w - n :=
  ⟨h.1, os_le n C hb (w - n) k h.2⟩

theorem reach_cases (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j k : ℕ)
    (h : OrReaches n C (n + j) k) :
    j < C.gates.length ∧ (k = j ∨ ((gateAt C j).op = GateOp.or ∧
      ∃ u ∈ (gateAt C j).inputs, u < n + j ∧ OrReaches n C u k)) := by
  obtain ⟨_, hmem⟩ := h
  rw [Nat.add_sub_cancel_left] at hmem
  obtain ⟨hj, hc⟩ := os_cases n C hb j k hmem
  refine ⟨hj, ?_⟩
  rcases hc with hkj | ⟨hor, u, hu, hnu, hul, hku⟩
  · exact Or.inl hkj
  · right
    rw [gateAt_eq C j hj]
    exact ⟨hor, u, hu, hul, hnu, hku⟩

theorem mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]

theorem orIn_sub (n : ℕ) (C : Circuit) (hb : ReadsBack n C) :
    ∀ w k, OrReaches n C w k → ∀ i, i ∈ orIn n C (n + k) → i ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro k hr i hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr.1
  obtain ⟨hj, hc⟩ := reach_cases n C hb j k hr
  rcases hc with hkj | ⟨hor, u, hu, hul, hru⟩
  · rw [hkj] at hi; exact hi
  · have h1 := ih u hul k hru i hi
    rw [gateAt_eq C j hj] at hor hu
    exact orIn_lift n C hb j hj hor u hu i h1

theorem orIn_gate (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (j : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C (n + j)) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      ∃ u ∈ (gateAt C j).inputs, u < n + j ∧ i ∈ orIn n C u := by
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨k, hk, hr, hko, hik⟩
  · have := i.isLt; omega
  · obtain ⟨hj, hc⟩ := reach_cases n C hb j k hr
    rcases hc with hkj | ⟨hor, u, hu, hul, hru⟩
    · rw [hkj] at hko hik
      refine ⟨hj, hko, i.val, hik, ?_, ?_⟩
      · have := i.isLt; omega
      · rw [mem_orIn]; exact Or.inl rfl
    · refine ⟨hj, hor, u, hu, hul, ?_⟩
      rw [mem_orIn]; exact Or.inr ⟨k, hk, hru, hko, hik⟩

theorem orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (i : Fin n)
    (hi : i ∈ orIn n C w) : (i : ℕ) = w := by
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨k, _, hr, _, _⟩
  · exact hi
  · have := hr.1; omega

theorem key (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    ∀ m (W : Finset ℕ), (∀ w ∈ W, w < m) → ∀ (U : Finset (Fin n)),
      (∀ b ∈ U, ∃ w ∈ W, b ∈ orIn n C w) → ∀ (M : Finset ℕ),
      (∀ k, (gateAt C k).op = GateOp.or → 2 ≤ (orIn n C (n + k)).card →
        (∃ w ∈ W, OrReaches n C w k) → k ∈ M) →
      U.card ≤ M.card + W.card := by
  classical
  have hb := hC.2.1
  intro m
  induction m with
  | zero =>
    intro W hW U hU M _
    have hUe : U = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro b hbU
      obtain ⟨w, hw, _⟩ := hU b hbU
      exact absurd (hW w hw) (by omega)
    simp [hUe]
  | succ m ih =>
    intro W hW U hU M hM
    by_cases hmW : m ∈ W
    swap
    · apply ih W (fun w hw => ?_) U hU M hM
      have h1 := hW w hw
      have h2 : w ≠ m := fun h => hmW (h ▸ hw)
      omega
    have hW0 : ∀ w ∈ W.erase m, w < m := by
      intro w hw
      have h1 := Finset.mem_erase.mp hw
      have h2 := hW w h1.2
      have h3 := h1.1
      omega
    have hcardW : (W.erase m).card + 1 = W.card := Finset.card_erase_add_one hmW
    have hM0 : ∀ k, (gateAt C k).op = GateOp.or → 2 ≤ (orIn n C (n + k)).card →
        (∃ w ∈ W.erase m, OrReaches n C w k) → k ∈ M := by
      intro k h1 h2 ⟨w, hw, hr⟩
      exact hM k h1 h2 ⟨w, (Finset.mem_erase.mp hw).2, hr⟩
    by_cases hin : m < n
    · have h0 := ih (W.erase m) hW0 (U.filter (fun b => ∃ w ∈ W.erase m, b ∈ orIn n C w))
        (fun b hb0 => (Finset.mem_filter.mp hb0).2) M hM0
      have hrest : (U \ U.filter (fun b => ∃ w ∈ W.erase m, b ∈ orIn n C w)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        have ex : ∀ z ∈ U \ U.filter (fun b => ∃ w ∈ W.erase m, b ∈ orIn n C w),
            (z : ℕ) = m := by
          intro z hz
          obtain ⟨hzU, hnot⟩ := Finset.mem_sdiff.mp hz
          obtain ⟨w, hw, hzw⟩ := hU z hzU
          by_cases hwm : w = m
          · rw [hwm] at hzw; exact orIn_input n C m hin z hzw
          · exact absurd (Finset.mem_filter.mpr
              ⟨hzU, w, Finset.mem_erase.mpr ⟨hwm, hw⟩, hzw⟩) hnot
        intro x hx y hy
        exact Fin.ext ((ex x hx).trans (ex y hy).symm)
      have hsplit := Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset (fun b => ∃ w ∈ W.erase m, b ∈ orIn n C w) U)
      omega
    obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
    by_cases hemp : orIn n C (n + j) = ∅
    · have h0 := ih (W.erase (n + j)) hW0 U (by
        intro b hbU
        obtain ⟨w, hw, hbw⟩ := hU b hbU
        by_cases hwm : w = n + j
        · rw [hwm, hemp] at hbw; simp at hbw
        · exact ⟨w, Finset.mem_erase.mpr ⟨hwm, hw⟩, hbw⟩) M hM0
      omega
    obtain ⟨b0, hb0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨hj, hor, x0, hx0, hx0lt, hb0x⟩ := orIn_gate n C hb j b0 hb0
    have hgm : C.gates[j] ∈ C.gates := List.getElem_mem hj
    have hl2 := hC.2.2 _ hgm
    rw [gateAt_eq C j hj] at hor hx0
    obtain ⟨u, v, hin2⟩ : ∃ u v, C.gates[j].inputs = [u, v] := by
      match h : C.gates[j].inputs, hl2 with
      | [u, v], _ => exact ⟨u, v, rfl⟩
    have hu : u < n + j := hb j hj u (by rw [gateAt_eq C j hj, hin2]; simp)
    have hv : v < n + j := hb j hj v (by rw [gateAt_eq C j hj, hin2]; simp)
    have hum : u ∈ C.gates[j].inputs := by rw [hin2]; simp
    have hvm : v ∈ C.gates[j].inputs := by rw [hin2]; simp
    by_cases hmer : 2 ≤ (orIn n C (n + j)).card
    · have hjM : j ∈ M := hM j (by rw [gateAt_eq C j hj]; exact hor) hmer
        ⟨n + j, hmW, reach_self n C j hj⟩
      have h0 := ih (insert u (insert v (W.erase (n + j)))) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with h | hw
          · omega
          rcases Finset.mem_insert.mp hw with h | hw
          · omega
          exact hW0 w hw) U (by
          intro b hbU
          obtain ⟨w, hw, hbw⟩ := hU b hbU
          by_cases hwm : w = n + j
          · rw [hwm] at hbw
            obtain ⟨_, _, x, hx, _, hbx⟩ := orIn_gate n C hb j b hbw
            rw [gateAt_eq C j hj, hin2] at hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact ⟨x, Finset.mem_insert_self _ _, hbx⟩
            · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hbx⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hwm, hw⟩)), hbw⟩) (M.erase j) (by
          intro k h1 h2 ⟨w, hw, hr⟩
          have hbd := reach_bound n C hb w k hr
          have hwlt : w < n + j := by
            rcases Finset.mem_insert.mp hw with h | hw
            · omega
            rcases Finset.mem_insert.mp hw with h | hw
            · omega
            exact hW0 w hw
          refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
          rcases Finset.mem_insert.mp hw with h | hw
          · rw [h] at hr
            exact hM k h1 h2 ⟨n + j, hmW, reach_lift n C hb j hj hor u hum k hr⟩
          rcases Finset.mem_insert.mp hw with h | hw
          · rw [h] at hr
            exact hM k h1 h2 ⟨n + j, hmW, reach_lift n C hb j hj hor v hvm k hr⟩
          exact hM k h1 h2 ⟨w, (Finset.mem_erase.mp hw).2, hr⟩)
      have c1 := Finset.card_erase_add_one hjM
      have c2 := Finset.card_insert_le u (insert v (W.erase (n + j)))
      have c3 := Finset.card_insert_le v (W.erase (n + j))
      omega
    · have hone : ∀ b ∈ orIn n C (n + j), b = b0 := by
        intro b hbm
        exact Finset.card_le_one.mp (by omega) b hbm b0 hb0
      have h0 := ih (insert x0 (W.erase (n + j))) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with h | hw
          · omega
          exact hW0 w hw) U (by
          intro b hbU
          obtain ⟨w, hw, hbw⟩ := hU b hbU
          by_cases hwm : w = n + j
          · rw [hwm] at hbw
            rw [hone b hbw]
            exact ⟨x0, Finset.mem_insert_self _ _, hb0x⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hw⟩), hbw⟩) M (by
          intro k h1 h2 ⟨w, hw, hr⟩
          rcases Finset.mem_insert.mp hw with h | hw
          · rw [h] at hr
            exact hM k h1 h2 ⟨n + j, hmW, reach_lift n C hb j hj hor x0 hx0 k hr⟩
          exact hM k h1 h2 ⟨w, (Finset.mem_erase.mp hw).2, hr⟩)
      have c2 := Finset.card_insert_le x0 (W.erase (n + j))
      omega

end Count

end PEqualNP.Outside.L_meta_2234

open PEqualNP.Outside.L_meta_2234
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.L_meta_2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf hG hC hz hadj
  have hb := hC.2.1
  refine ⟨?_, ?_⟩
  · intro i hi hor hcard _ hreach
    obtain ⟨b, hbmem⟩ : ∃ b, b ∈ orIn n C (n + i) := by
      apply Finset.card_pos.mp; omega
    have h1 := sem_orIn n C hb b (n + i) hbmem
    have h2 := sem_reach n C hb (fun k => decide (k = b)) C.output i hreach h1
    have h3 := hz b
    simp only [circuitFun, Circuit.eval] at h3
    rw [h2] at h3; exact absurd h3 (by simp)
  · classical
    obtain ⟨Mc, hMc⟩ : ∃ Mc : Fin n → Finset ℕ, ∀ c k, k ∈ Mc c ↔
        (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ 2 ≤ (orIn n C (n + k)).card ∧
          ∃ j ∈ F, ctr j = c ∧ OrReaches n C (lf j) k) :=
      ⟨fun c => (Finset.range C.gates.length).filter (fun k => (gateAt C k).op = GateOp.or ∧
        2 ≤ (orIn n C (n + k)).card ∧ ∃ j ∈ F, ctr j = c ∧ OrReaches n C (lf j) k),
        fun c k => by simp only [Finset.mem_filter, Finset.mem_range]⟩
    refine le_trans (Finset.sum_le_sum
      (g := fun c => (Mc c).card + (F.filter (fun j => ctr j = c)).card) (fun c _ => ?_)) ?_
    · refine le_trans (key n C hC ((((F.filter (fun j => ctr j = c)).image lf).sup id) + 1)
        ((F.filter (fun j => ctr j = c)).image lf) ?_ _ ?_ (Mc c) ?_)
        (Nat.add_le_add_left Finset.card_image_le _)
      · intro w hw
        exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hw)
      · intro b hbm
        obtain ⟨j, hjF, hjc, hbj⟩ := (Finset.mem_filter.mp hbm).2
        exact ⟨lf j, Finset.mem_image_of_mem lf (Finset.mem_filter.mpr ⟨hjF, hjc⟩), hbj⟩
      · intro k h1 h2 ⟨w, hw, hr⟩
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hj' := Finset.mem_filter.mp hj
        have hbd := reach_bound n C hb (lf j) k hr
        exact (hMc c k).mpr ⟨by omega, h1, h2, j, hj'.1, hj'.2, hr⟩
    · rw [Finset.sum_add_distrib]
      have hF : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
        (Finset.card_eq_sum_card_fiberwise (f := ctr) (s := F) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)).symm
      have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Mc := by
        intro c _ c' _ hne
        show Disjoint (Mc c) (Mc c')
        rw [Finset.disjoint_left]
        intro k hk hk'
        obtain ⟨_, _, hcard, j, hjF, hjc, hr⟩ := (hMc c k).mp hk
        obtain ⟨_, _, _, j', hjF', hjc', hr'⟩ := (hMc c' k).mp hk'
        have s1 := orIn_sub n C hb (lf j) k hr
        have s2 := orIn_sub n C hb (lf j') k hr'
        have hG' := hG c c' hne
        have h2 : (orIn n C (n + k)).card ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) hG'
          intro b hbm
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · rw [← hjc]; exact hadj j hjF b (s1 b hbm)
          · rw [← hjc']; exact hadj j' hjF' b (s2 b hbm)
        omega
      have hM : ∑ c : Fin n, (Mc c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧ 2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} := by
        rw [← Finset.card_biUnion hdisj, ← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard
        · intro k hk
          rw [Finset.mem_coe, Finset.mem_biUnion] at hk
          obtain ⟨c, _, hkc⟩ := hk
          obtain ⟨h1, h2, h3, j, hjF, _, hr⟩ := (hMc c k).mp hkc
          exact ⟨h1, h2, h3, j, hjF, hr⟩
        · exact (Set.finite_lt_nat C.gates.length).subset (fun k hk => hk.1)
      exact Nat.add_le_add hM (le_of_eq hF)
