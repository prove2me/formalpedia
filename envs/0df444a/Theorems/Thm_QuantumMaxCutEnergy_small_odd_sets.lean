-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_small_odd_sets
-- name    : QuantumMaxCutEnergy.small_odd_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:37:16.624972+00:00
-- url     : https://prove2.me/theorems/2f81ec47-aeec-4596-9c79-efe7d419e817
-- title:
--   Small odd-set constraints yield a scaled fractional matching
-- statement:
--   Nonnegative edge values satisfying vertex capacities and all small odd-set inequalities satisfy every matching-polytope inequality after scaling by q/(q+1).
-- source:
--   Lee and Parekh, ICALP2024, Lemma9 (the 4/5 case), https://doi.org/10.4230/LIPIcs.ICALP.2024.105 ; Gribling, Sinjorgo and Sotirov, arXiv2504.11120v1, Lemma3.4 and Corollary3.6, https://arxiv.org/html/2504.11120v1 . Generalized finite small-odd-set scaling q/(q+1); does not assert matching-polytope integrality or a solver.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.small_odd_sets
    {n : ℕ} (q : ℕ) (x : QuantumMaxCutEnergy.Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n,
      (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hsmall : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ q →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤ ((S.card : ℝ) - 1) / 2) :
    (∀ e, 0 ≤ ((q : ℝ) / (q + 1)) * x e) ∧
    (∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then
      ((q : ℝ) / (q + 1)) * x e else 0) ≤ 1) ∧
    (∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), ((q : ℝ) / (q + 1)) * x e) ≤
        ((S.card : ℝ) - 1) / 2) := by sorry
