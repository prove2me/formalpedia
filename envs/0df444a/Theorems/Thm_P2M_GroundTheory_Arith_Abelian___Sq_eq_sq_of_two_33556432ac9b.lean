-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b
-- name    : P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:28.325846+00:00
-- url     : https://prove2.me/theorems/0f34ffb9-90ff-4344-b21a-7ba10bb56167
-- title:
--   P2 M Ground Theory Arith Abelian   Sq eq sq of two 33556432ac9b: P2 M Ground Theory Arith Abelian   Sq eq sq of two 33556432ac9b
-- statement:
--   The P2 M Ground Theory Arith Abelian   Sq eq sq of two 33556432ac9b construction uses the P2 M Ground Theory Arith Abelian   Sq eq sq of two 33556432ac9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L109-L117

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

theorem P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b (h2 : p = 2) : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 := by sorry

alias «GroundTheory».«Arith».«Abelian».«Ψ₂Sq_eq_sq_of_two» := P2M_GroundTheory_Arith_Abelian___Sq_eq_sq_of_two_33556432ac9b
