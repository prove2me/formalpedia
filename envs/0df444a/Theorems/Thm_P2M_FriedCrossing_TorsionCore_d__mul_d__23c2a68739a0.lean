-- Prove2me | Theorems.Thm_P2M_FriedCrossing_TorsionCore_d__mul_d__23c2a68739a0
-- name    : P2M_FriedCrossing_TorsionCore_d__mul_d__23c2a68739a0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:02.862175+00:00
-- url     : https://prove2.me/theorems/8a80cb80-a9fc-5329-bcb6-eb4a357556af
-- title:
--   P2 M Fried Crossing Torsion Core d  mul d  23c2a68739a0: P2 M Fried Crossing Torsion Core d  mul d  23c2a68739a0
-- statement:
--   The P2 M Fried Crossing Torsion Core d  mul d  23c2a68739a0 construction uses the P2 M Fried Crossing Torsion Core d  mul d  23c2a68739a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L57-L60
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L57-L60

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem P2M_FriedCrossing_TorsionCore_d__mul_d__23c2a68739a0 (x l : K) : d₂ x l * (d₁ : Matrix (Fin 3) (Fin 1) K) = 0 := by sorry

alias «FriedCrossing».«TorsionCore».«d₂_mul_d₁» := P2M_FriedCrossing_TorsionCore_d__mul_d__23c2a68739a0
