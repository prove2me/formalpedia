-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateTrianglePointsQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.stateTrianglePointsQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:02:28.097207+00:00
-- url     : https://prove2.me/theorems/41e9d501-1516-4334-a6e9-c138b4090bf8
-- title:
--   BDL26 Random Perturbation: state Triangle Points Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the state Triangle Points Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L27-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L27-L37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateTrianglePointsQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (stateTrianglePointsQuery P J lambda t R).2 ≤ 153+6*R.length := by sorry
