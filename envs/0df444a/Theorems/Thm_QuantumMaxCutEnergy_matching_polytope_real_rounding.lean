-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_real_rounding
-- name    : QuantumMaxCutEnergy.matching_polytope_real_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:30:07.37421+00:00
-- url     : https://prove2.me/theorems/a120bf4f-da23-4f6c-afd4-b501b8ce3f04
-- title:
--   Edmonds' matching polytope theorem for real weights
-- statement:
--   Let $x\ge 0$ be an edge vector on the complete graph on $n$ vertices with $x(\delta(v))\le 1$ for every vertex $v$ and $x(E[S])\le(|S|-1)/2$ for every odd vertex set $S$. Then for every nonnegative real weight vector $w$ there is a matching $M$ with
--
--   $$\sum_e w_ex_e\le\sum_{e\in M}w_e .$$
--
--   This extends the rational-weight statement by approximating $w$ from below by rationals and using that there are finitely many matchings.
-- source:
--   Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B, 1965; real weights are needed for the reweighted matching step of Apte, Lee, Marwaha, Parekh and Sud, ESA 2025, https://doi.org/10.4230/LIPIcs.ESA.2025.101, Algorithm 2 and Eq. (16).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.matching_polytope_real_rounding {n : ℕ}
    (w : QuantumMaxCutEnergy.Edge n → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : QuantumMaxCutEnergy.Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤ ((S.card : ℝ) - 1) / 2) :
    ∃ M : Finset (QuantumMaxCutEnergy.Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ e, w e * x e) ≤ ∑ e ∈ M, w e := by sorry
