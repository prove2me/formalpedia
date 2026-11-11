-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_refreshStateRowQuery_member
-- name    : QEC.Coding.BDL26RandomPerturbation.refreshStateRowQuery_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:56:52.915584+00:00
-- url     : https://prove2.me/theorems/2cc3ec0b-34fe-4a73-af95-ef0990babe70
-- title:
--   BDL26 Random Perturbation: refresh State Row Query member
-- statement:
--   The BDL26 Random Perturbation construction uses the refresh State Row Query member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L91-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/StateRows.lean#L91-L93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExecutionPrimitiveQueries
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
variable {P : TannerSquarePresentation}

theorem QEC.Coding.BDL26RandomPerturbation.refreshStateRowQuery_member (support : List (Vertex P)) (v : Vertex P) :
    (memberQuery (fun v w : Vertex P => (decide (v=w),1)) v support).1 = true ↔ v ∈ support := by sorry
