-- Prove2me | Theorems.Thm_P2M_FriedCrossing_TorsionCore_d__mul_d__53f55e44f3e8
-- name    : P2M_FriedCrossing_TorsionCore_d__mul_d__53f55e44f3e8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:08.798822+00:00
-- url     : https://prove2.me/theorems/8aca7f6c-fe2a-5939-8725-8539aa2061a5
-- title:
--   P2 M Fried Crossing Torsion Core d  mul d  53f55e44f3e8: P2 M Fried Crossing Torsion Core d  mul d  53f55e44f3e8
-- statement:
--   The P2 M Fried Crossing Torsion Core d  mul d  53f55e44f3e8 construction uses the P2 M Fried Crossing Torsion Core d  mul d  53f55e44f3e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L62-L65
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L62-L65

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem P2M_FriedCrossing_TorsionCore_d__mul_d__53f55e44f3e8 (x l : K) : d₃ l * d₂ x l = 0 := by sorry

alias «FriedCrossing».«TorsionCore».«d₃_mul_d₂» := P2M_FriedCrossing_TorsionCore_d__mul_d__53f55e44f3e8
