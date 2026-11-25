-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819
-- name    : P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:27.448803+00:00
-- url     : https://prove2.me/theorems/6cfe7490-88ee-4954-aaba-77a600b0af31
-- title:
--   P2 M Ground Theory Arith Abelian is Coprime    Sq a9e3a7b07819: P2 M Ground Theory Arith Abelian is Coprime    Sq a9e3a7b07819
-- statement:
--   The P2 M Ground Theory Arith Abelian is Coprime    Sq a9e3a7b07819 construction uses the P2 M Ground Theory Arith Abelian is Coprime    Sq a9e3a7b07819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L74-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L74-L107

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]

theorem P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819 (n : ℤ) : IsCoprime (W.Φ n) (W.ΨSq n) := by sorry

alias «GroundTheory».«Arith».«Abelian».«isCoprime_Φ_ΨSq» := P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819
