-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stateTriangleQuery_correct
-- name    : QEC.Coding.BDL26RandomPerturbation.stateTriangleQuery_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:04:03.493427+00:00
-- url     : https://prove2.me/theorems/1f44a615-7f7c-4521-b369-395c120119f6
-- title:
--   BDL26 Random Perturbation: state Triangle Query correct
-- statement:
--   The BDL26 Random Perturbation construction uses the state Triangle Query correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateEventQuery.lean#L45-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.stateTriangleQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (t : Triangle P) (R : StateRows P) (z : Space) :
    (stateTriangleQuery P J lambda t R z).1 = true ↔
      (fun i => statePoints R (triangleVertex P t i)) ∈
        triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P t i))) z 2 := by sorry
