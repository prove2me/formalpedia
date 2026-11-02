-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_polynomialTime_max_from_explicit_programs
-- name    : QuantumMaxCutEnergy.polynomialTime_max_from_explicit_programs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:32:15.300118+00:00
-- url     : https://prove2.me/theorems/42066501-296a-48de-a706-0c4d4dc27ab8
-- title:
--   Certified maximum composition of explicit finite classical programs
-- statement:
--   Given explicit finite Boolean-stack polynomial-time programs for the rational outputs of a campaign algorithm A and a deterministic estimator b, the algorithm returning max(b(G),A(G,R)) has a genuine polynomial-time TM2 certificate in the canonical campaign output encoding. It retains the same prescribed random-bit parameters. This is the concrete program-composition theorem used by the current campaign reductions. Approximation and soundness hypotheses are unnecessary for this runtime theorem.
-- source:
--   The finite Boolean-machine exact rational comparison and composition infrastructure used by the accepted QuantumMaxCutEnergy matching/forest implementation. Mathematical role: selecting the best numerical candidate in AGM2020 Theorem3, https://doi.org/10.4230/LIPIcs.TQC.2020.7 . This theorem concerns the explicit compiler witnesses and canonical output conversion.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

theorem QuantumMaxCutEnergy.polynomialTime_max_from_explicit_programs
    (A : QuantumMaxCutEnergy.Algorithm) (b : QuantumMaxCutEnergy.Input → ℚ≥0)
    (Pb : OAI.MetricKMedian.Binary.PolyProgram
      QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
      (fun req : QuantumMaxCutEnergy.Input × List Bool => (b req.1 : ℚ)))
    (PA : OAI.MetricKMedian.Binary.PolyProgram
      QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
      (fun req : QuantumMaxCutEnergy.Input × List Bool => (A.run req.1 req.2 : ℚ))) :
    QuantumMaxCutEnergy.PolynomialTime
      { randomFactor := A.randomFactor
        randomDegree := A.randomDegree
        run := fun G r => max (b G) (A.run G r) } := by sorry
