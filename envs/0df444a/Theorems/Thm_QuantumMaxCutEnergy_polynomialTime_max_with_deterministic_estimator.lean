-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_polynomialTime_max_with_deterministic_estimator
-- name    : QuantumMaxCutEnergy.polynomialTime_max_with_deterministic_estimator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:26:03.037598+00:00
-- url     : https://prove2.me/theorems/7b09ddeb-0317-42a9-99ac-96c5dc0f1b9d
-- title:
--   Polynomial-time closure under a deterministic rational maximum
-- statement:
--   If P is a polynomial-time campaign algorithm and a deterministic nonnegative rational estimator b has a polynomial-time certificate on the campaign request encoding, then returning max(b(G),P(G,R)) with the same random-bit budget is also polynomial time. Both input computation certificates use the fixed canonical encodings, and the conclusion requires a genuine classical TM2 certificate. No approximation hypothesis or bound is assumed.
-- source:
--   Classical closure of polynomial-time computation under composition and exact comparison of canonically encoded nonnegative rational outputs. Supporting implementation lemma for AGM TQC2020 Theorem3, max of candidate values, p7:10. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . This is a computational closure obligation, not an assumed approximation theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.polynomialTime_max_with_deterministic_estimator
    (P : QuantumMaxCutEnergy.Algorithm) (b : QuantumMaxCutEnergy.Input → ℚ≥0)
    (hP : QuantumMaxCutEnergy.PolynomialTime P)
    (hb : Nonempty (Turing.TM2ComputableInPolyTime
      QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => b request.1))) :
    QuantumMaxCutEnergy.PolynomialTime
      { randomFactor := P.randomFactor
        randomDegree := P.randomDegree
        run := fun G r => max (b G) (P.run G r) } := by sorry
