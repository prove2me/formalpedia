-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_matching_forest_estimator_implementation
-- name    : QuantumMaxCutEnergy.agm_matching_forest_estimator_implementation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:26:04.287196+00:00
-- url     : https://prove2.me/theorems/7add9ec0-1b7b-4be4-a4a5-0e03f86effca
-- title:
--   Polynomial-time matching and forest numerical estimator
-- statement:
--   There is a deterministic nonnegative rational lower estimator b with a classical polynomial-time certificate in the campaign encoding. For every weighted graph G, write W for the total edge weight and O for its unrestricted QMC optimum. There are real auxiliary weights 0≤m≤f≤W such that O≤W+(m+f)/2 and b(G) dominates both f and (W+3m)/2, while b(G)≤O. The intended construction uses the matching and forest selected in AGM Lemma 7. The statement certifies the numerical bounds and runtime; it does not require a state as output.
-- source:
--   Anshu, Gosset and Morenz, TQC2020, Lemma5, Lemma7, Eq25 and Eq26, pp7:6–7:10. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . Numerical-estimation corollary with an explicit finite-bit uniform polynomial-time implementation obligation; not a verbatim standalone theorem in the paper.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_matching_forest_estimator_implementation :
    ∃ b : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime
        QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => b request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (b G : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
        ∃ m f : ℝ,
          0 ≤ m ∧ m ≤ f ∧ f ≤ (∑ e, (G.weights e : ℝ)) ∧
          QuantumMaxCutEnergy.optimum G ≤ (∑ e, (G.weights e : ℝ)) + (m + f) / 2 ∧
          f ≤ (b G : ℝ) ∧
          ((∑ e, (G.weights e : ℝ)) + 3 * m) / 2 ≤ (b G : ℝ) := by sorry
