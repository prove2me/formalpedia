-- Prove2me | Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6
-- name    : P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:28.731795+00:00
-- url     : https://prove2.me/theorems/fb8bab4d-e013-4471-988b-24bfdf875124
-- title:
--   P2 M Fried Crossing Torsion Core det D mat 4a6a93f491c6: P2 M Fried Crossing Torsion Core det D mat 4a6a93f491c6
-- statement:
--   The P2 M Fried Crossing Torsion Core det D mat 4a6a93f491c6 construction uses the P2 M Fried Crossing Torsion Core det D mat 4a6a93f491c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L71-L74
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L71-L74

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6 (x l : K) : (D₃mat x l).det = -(l + x) := by sorry

alias «FriedCrossing».«TorsionCore».«det_D₃mat» := P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6
