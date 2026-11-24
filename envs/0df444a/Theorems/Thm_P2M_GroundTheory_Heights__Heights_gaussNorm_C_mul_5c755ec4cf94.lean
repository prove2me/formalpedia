-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:25.449698+00:00
-- url     : https://prove2.me/theorems/f31c74fc-7c8f-4ae5-8071-b4e89855d2e5
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm C mul 5c755ec4cf94: P2 M Ground Theory Heights  Heights gauss Norm C mul 5c755ec4cf94
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm C mul 5c755ec4cf94 construction uses the P2 M Ground Theory Heights  Heights gauss Norm C mul 5c755ec4cf94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L171-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L171-L174

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

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K)
    (f : MvPolynomial ι K) :
    gaussNorm v (C c * f) = NumberField.HeightOneSpectrum.adicAbv K v c * gaussNorm v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_C_mul» := P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94
