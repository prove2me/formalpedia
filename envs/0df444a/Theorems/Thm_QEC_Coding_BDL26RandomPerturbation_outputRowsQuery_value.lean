-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_outputRowsQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.outputRowsQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:22:32.934195+00:00
-- url     : https://prove2.me/theorems/9ad3a4c3-205d-46d2-8983-3953a1cbf749
-- title:
--   BDL26 Random Perturbation: output Rows Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the output Rows Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L75-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L75-L79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.outputRowsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) :
    (outputRowsQuery P J lambda p).1 =
      (vertexInputList P).map (fun v => (v,lambda • ((1/2 : ℝ) • J v)+p v)) := by sorry
