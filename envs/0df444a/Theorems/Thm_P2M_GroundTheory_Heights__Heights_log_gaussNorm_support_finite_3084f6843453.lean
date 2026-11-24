-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453
-- name    : P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:59.126654+00:00
-- url     : https://prove2.me/theorems/7e734dc2-9cfe-469f-8dcc-eeea104580da
-- title:
--   P2 M Ground Theory Heights  Heights log gauss Norm support finite 3084f6843453: P2 M Ground Theory Heights  Heights log gauss Norm support finite 3084f6843453
-- statement:
--   The P2 M Ground Theory Heights  Heights log gauss Norm support finite 3084f6843453 construction uses the P2 M Ground Theory Heights  Heights log gauss Norm support finite 3084f6843453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L196-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L196-L216

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

theorem P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453 {ι : Type*} {f : MvPolynomial ι K} (hf : f ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v f)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«log_gaussNorm_support_finite» := P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453
