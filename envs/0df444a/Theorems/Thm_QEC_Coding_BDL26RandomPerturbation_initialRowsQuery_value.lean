-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_initialRowsQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:52:50.612844+00:00
-- url     : https://prove2.me/theorems/b06de040-b880-413b-aa48-2ed3244eaac7
-- title:
--   BDL26 Random Perturbation: initial Rows Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the initial Rows Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L26-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L26-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_value (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (initialRowsQuery P T).1 = (vertexInputList P).map (fun v => (v,0,T (v,0))) := by sorry
