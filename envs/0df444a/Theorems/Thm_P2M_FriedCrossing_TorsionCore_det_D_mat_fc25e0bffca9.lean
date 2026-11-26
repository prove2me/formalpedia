-- Prove2me | Theorems.Thm_P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9
-- name    : P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:20.879839+00:00
-- url     : https://prove2.me/theorems/4e6e8a03-e15e-4c97-8a86-1a7d950a3c84
-- title:
--   P2 M Fried Crossing Torsion Core det D mat fc25e0bffca9: P2 M Fried Crossing Torsion Core det D mat fc25e0bffca9
-- statement:
--   The P2 M Fried Crossing Torsion Core det D mat fc25e0bffca9 construction uses the P2 M Fried Crossing Torsion Core det D mat fc25e0bffca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L67-L69
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L67-L69

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9 : (D₂mat : Matrix (Fin 3) (Fin 3) K).det = -1 := by sorry

alias «FriedCrossing».«TorsionCore».«det_D₂mat» := P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9
