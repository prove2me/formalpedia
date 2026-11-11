-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateRowQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.stateRowQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:56:43.014604+00:00
-- url     : https://prove2.me/theorems/be9c7777-42f8-4fea-a5eb-077b0827e5b9
-- title:
--   BDL26 Random Perturbation: state Row Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the state Row Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L31-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L31-L37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.stateRowQuery_cost_le (v : Vertex P) (R : StateRows P) :
    (stateRowQuery v R).2 ≤ 2*R.length := by sorry
