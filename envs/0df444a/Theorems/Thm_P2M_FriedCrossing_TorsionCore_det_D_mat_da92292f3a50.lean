-- Prove2me | Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50
-- name    : P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:38.128399+00:00
-- url     : https://prove2.me/theorems/ffeecdd5-7bb6-47a0-97ae-83c5390e389f
-- title:
--   P2 M Fried Crossing Torsion Core det D mat da92292f3a50: P2 M Fried Crossing Torsion Core det D mat da92292f3a50
-- statement:
--   The P2 M Fried Crossing Torsion Core det D mat da92292f3a50 construction uses the P2 M Fried Crossing Torsion Core det D mat da92292f3a50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L76-L78
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L76-L78

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50 (l : K) : (D₄mat l).det = l := by sorry

alias «FriedCrossing».«TorsionCore».«det_D₄mat» := P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50
