-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_outputRowsQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.outputRowsQuery_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:22:04.517937+00:00
-- url     : https://prove2.me/theorems/0f7ae92d-044b-480e-9b46-c00a2facb7ef
-- title:
--   BDL26 Random Perturbation: output Rows Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the output Rows Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L81-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L81-L90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.outputRowsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (p : Vertex P → Space) :
    (outputRowsQuery P J lambda p).2 ≤ 49*Fintype.card (Vertex P) := by sorry
