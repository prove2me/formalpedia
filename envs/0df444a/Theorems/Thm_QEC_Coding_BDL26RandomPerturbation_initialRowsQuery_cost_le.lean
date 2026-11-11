-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_initialRowsQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:52:45.091297+00:00
-- url     : https://prove2.me/theorems/c0652762-6d3c-41b4-b023-85e4b2d272c0
-- title:
--   BDL26 Random Perturbation: initial Rows Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the initial Rows Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L31-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExecutionPrimitiveQueries.lean#L31-L35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26RandomPerturbation.initialRowsQuery_cost_le (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) :
    (initialRowsQuery P T).2 ≤ 5*Fintype.card (Vertex P) := by sorry
