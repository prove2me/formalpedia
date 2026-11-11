-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_StateRowsRep_points
-- name    : QEC.Coding.BDL26RandomPerturbation.StateRowsRep_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:57:43.442199+00:00
-- url     : https://prove2.me/theorems/b24b3ad8-9047-44f6-aac8-10ff25a0ece9
-- title:
--   BDL26 Random Perturbation: State Rows Rep points
-- statement:
--   The BDL26 Random Perturbation construction uses the State Rows Rep points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L62-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L62-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.StateRowsRep_points (P : TannerSquarePresentation) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) (R : StateRows P) (hR : StateRowsRep P T c R) :
    statePoints R = assignment T c := by sorry
