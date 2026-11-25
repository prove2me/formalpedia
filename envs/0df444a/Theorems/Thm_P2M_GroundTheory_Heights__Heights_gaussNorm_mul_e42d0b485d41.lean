-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:06.842086+00:00
-- url     : https://prove2.me/theorems/eeae43de-8c89-4339-b736-0d0f1b4c8cf2
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm mul e42d0b485d41: P2 M Ground Theory Heights  Heights gauss Norm mul e42d0b485d41
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm mul e42d0b485d41 construction uses the P2 M Ground Theory Heights  Heights gauss Norm mul e42d0b485d41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L163-L165

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
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f g : MvPolynomial ι K) : gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_mul» := P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
