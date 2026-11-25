-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:11.023244+00:00
-- url     : https://prove2.me/theorems/fad98699-93a8-44e8-afc0-4d73aabad472
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of mul ff1ac2fe2a0f: P2 M Ground Theory Heights  Heights gauss Norm Of mul ff1ac2fe2a0f
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of mul ff1ac2fe2a0f construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of mul ff1ac2fe2a0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L145-L151

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
variable {w}

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) = gaussNormOf w f * gaussNormOf w g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_mul» := P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f
