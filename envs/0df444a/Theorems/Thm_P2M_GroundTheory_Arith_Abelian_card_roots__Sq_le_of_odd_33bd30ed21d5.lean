-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5
-- name    : P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:29.995795+00:00
-- url     : https://prove2.me/theorems/a11e8543-667b-59e9-99c9-fe3db2d7bf90
-- title:
--   P2 M Ground Theory Arith Abelian card roots  Sq le of odd 33bd30ed21d5: P2 M Ground Theory Arith Abelian card roots  Sq le of odd 33bd30ed21d5
-- statement:
--   The P2 M Ground Theory Arith Abelian card roots  Sq le of odd 33bd30ed21d5 construction uses the P2 M Ground Theory Arith Abelian card roots  Sq le of odd 33bd30ed21d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L87-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L87-L107

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]

theorem P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5 (hodd : p ≠ 2) :
    (E.ΨSq p).roots.toFinset.card ≤ (p ^ 2 - 1) / 2 - 1 := by sorry

alias «GroundTheory».«Arith».«Abelian».«card_roots_ΨSq_le_of_odd» := P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5
