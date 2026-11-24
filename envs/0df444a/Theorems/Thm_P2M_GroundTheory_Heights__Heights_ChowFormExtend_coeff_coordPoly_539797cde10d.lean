-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:16.686943+00:00
-- url     : https://prove2.me/theorems/0906d833-4ecd-4f3c-a363-dc847ebc3644
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend coeff coord Poly 539797cde10d: P2 M Ground Theory Heights  Heights Chow Form Extend coeff coord Poly 539797cde10d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend coeff coord Poly 539797cde10d construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend coeff coord Poly 539797cde10d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L92-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d (φ : L →ₗ[K] K) (p : MvPolynomial Y L) (m : Y →₀ ℕ) :
    coeff m (coordPoly φ p) = φ (coeff m p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«coeff_coordPoly» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
