-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateTriangleQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.stateTriangleQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:04:15.18711+00:00
-- url     : https://prove2.me/theorems/e6893db5-b23d-4051-86d4-5f7c69bb44be
-- title:
--   BDL26 Random Perturbation: state Triangle Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the state Triangle Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L53-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L53-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateTriangleQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (stateTriangleQuery P J lambda t R z).2 ≤ 200200+6*R.length := by sorry
