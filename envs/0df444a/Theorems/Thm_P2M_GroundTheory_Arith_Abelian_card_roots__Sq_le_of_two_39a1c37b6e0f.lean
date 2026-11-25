-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f
-- name    : P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:42.983815+00:00
-- url     : https://prove2.me/theorems/2b897467-804a-4604-8104-cc192677e524
-- title:
--   P2 M Ground Theory Arith Abelian card roots  Sq le of two 39a1c37b6e0f: P2 M Ground Theory Arith Abelian card roots  Sq le of two 39a1c37b6e0f
-- statement:
--   The P2 M Ground Theory Arith Abelian card roots  Sq le of two 39a1c37b6e0f construction uses the P2 M Ground Theory Arith Abelian card roots  Sq le of two 39a1c37b6e0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L119-L125

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

theorem P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f (h2 : p = 2) : (E.ΨSq p).roots.toFinset.card ≤ 1 := by sorry

alias «GroundTheory».«Arith».«Abelian».«card_roots_ΨSq_le_of_two» := P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f
