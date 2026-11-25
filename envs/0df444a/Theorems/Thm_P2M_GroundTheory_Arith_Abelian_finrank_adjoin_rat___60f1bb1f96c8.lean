-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8
-- name    : P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:54.957678+00:00
-- url     : https://prove2.me/theorems/70490610-f577-40c9-a3f0-b0f521494164
-- title:
--   P2 M Ground Theory Arith Abelian finrank adjoin rat   60f1bb1f96c8: P2 M Ground Theory Arith Abelian finrank adjoin rat   60f1bb1f96c8
-- statement:
--   The P2 M Ground Theory Arith Abelian finrank adjoin rat   60f1bb1f96c8 construction uses the P2 M Ground Theory Arith Abelian finrank adjoin rat   60f1bb1f96c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L219-L221

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
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
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8 {n : ℤ} (hn : n ≠ 0) :
    Module.finrank (IntermediateField.adjoin F {ratΦΨ E n}) (RatFunc F) = n.natAbs ^ 2 := by sorry

alias «GroundTheory».«Arith».«Abelian».«finrank_adjoin_ratΦΨ» := P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8
