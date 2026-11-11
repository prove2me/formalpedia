-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateTrianglePointsQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.stateTrianglePointsQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:01:40.40973+00:00
-- url     : https://prove2.me/theorems/8a2ddcbc-0297-41f8-ab69-d433a37278f8
-- title:
--   BDL26 Random Perturbation: state Triangle Points Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the state Triangle Points Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L20-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L20-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateTrianglePointsQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) :
    (stateTrianglePointsQuery P J lambda t R).1 =
      fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P t i))+statePoints R (triangleVertex P t i) := by sorry
