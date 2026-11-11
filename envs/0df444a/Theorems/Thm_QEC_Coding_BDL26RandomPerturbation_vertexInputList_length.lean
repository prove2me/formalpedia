-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_length
-- name    : QEC.Coding.BDL26RandomPerturbation.vertexInputList_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:50:29.809759+00:00
-- url     : https://prove2.me/theorems/3d5dd391-1ca5-48f4-a9dd-043254699615
-- title:
--   BDL26 Random Perturbation: vertex Input List length
-- statement:
--   The BDL26 Random Perturbation construction uses the vertex Input List length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L14-L15
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L14-L15

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.vertexInputList_length (P : TannerSquarePresentation) :
    (vertexInputList P).length = Fintype.card (Vertex P) := by sorry
