-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:57.274614+00:00
-- url     : https://prove2.me/theorems/2306797f-fc68-4c8a-ad0c-ec26dbf9d4b5
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of mul le e992443b279f: P2 M Ground Theory Heights  Heights gauss Norm Of mul le e992443b279f
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of mul le e992443b279f construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of mul le e992443b279f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L71-L80

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

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) ≤ gaussNormOf w f * gaussNormOf w g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_mul_le» := P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
