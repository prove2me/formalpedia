-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_positive_excess
-- name    : QuantumMaxCutEnergy.positive_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:37:20.383661+00:00
-- url     : https://prove2.me/theorems/f3d1dd95-649c-4a64-a02a-6f7a4b9fea2d
-- title:
--   Unweighted subgraph bounds control positive energy excess
-- statement:
--   Selecting the positive-excess edges turns bounds for every unweighted subgraph into the matching odd-set inequality. This links finite spectral certificates to weighted matching reductions.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv2504.11120v1, Lemma3.5, https://arxiv.org/html/2504.11120v1 . Finite positive-excess edge selection used to derive matching odd-set constraints from unweighted subgraph energy bounds; spectral bounds are explicit hypotheses.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.positive_excess
    {n : ℕ} (g : QuantumMaxCutEnergy.Edge n → ℝ) (S : Finset (Fin n))
    (hsubgraph : ∀ F : Finset (QuantumMaxCutEnergy.Edge n),
      F ⊆ Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S) →
      (∑ e ∈ F, g e) ≤ (F.card : ℝ) + ((S.card : ℝ) - 1) / 2) :
    (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
      e.val.1 ∈ S ∧ e.val.2 ∈ S)), max (g e - 1) 0) ≤
      ((S.card : ℝ) - 1) / 2 := by sorry
