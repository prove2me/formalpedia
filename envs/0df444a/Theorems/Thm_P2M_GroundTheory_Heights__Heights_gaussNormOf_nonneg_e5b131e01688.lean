-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:17.482638+00:00
-- url     : https://prove2.me/theorems/341014c6-0c95-45e6-b9ee-6fb22aa4e667
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of nonneg e5b131e01688: P2 M Ground Theory Heights  Heights gauss Norm Of nonneg e5b131e01688
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of nonneg e5b131e01688 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of nonneg e5b131e01688 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L23-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
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
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688 (f : MvPolynomial ι R) : 0 ≤ gaussNormOf w f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_nonneg» := P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
