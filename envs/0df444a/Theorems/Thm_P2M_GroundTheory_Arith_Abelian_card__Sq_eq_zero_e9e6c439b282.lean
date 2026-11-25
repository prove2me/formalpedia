-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_card__Sq_eq_zero_e9e6c439b282
-- name    : P2M_GroundTheory_Arith_Abelian_card__Sq_eq_zero_e9e6c439b282
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:08.57681+00:00
-- url     : https://prove2.me/theorems/c7181255-250f-56fb-af6a-5c0c2c4e2a99
-- title:
--   P2 M Ground Theory Arith Abelian card  Sq eq zero e9e6c439b282: P2 M Ground Theory Arith Abelian card  Sq eq zero e9e6c439b282
-- statement:
--   The P2 M Ground Theory Arith Abelian card  Sq eq zero e9e6c439b282 construction uses the P2 M Ground Theory Arith Abelian card  Sq eq zero e9e6c439b282 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L357-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L357-L361

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian_card__Sq_eq_zero_e9e6c439b282 {n : ℤ} (hn : (n : F) ≠ 0) :
    Nat.card {P : W.toAffine.Point // P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0} = n.natAbs ^ 2 := by sorry

alias «GroundTheory».«Arith».«Abelian».«card_ΨSq_eq_zero» := P2M_GroundTheory_Arith_Abelian_card__Sq_eq_zero_e9e6c439b282
