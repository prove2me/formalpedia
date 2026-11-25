-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:37.938155+00:00
-- url     : https://prove2.me/theorems/8f681861-4473-4d55-9198-33ea8d99c1e5
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm nonneg 6ba4fe626cee: P2 M Ground Theory Heights  Heights gauss Norm nonneg 6ba4fe626cee
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm nonneg 6ba4fe626cee construction uses the P2 M Ground Theory Heights  Heights gauss Norm nonneg 6ba4fe626cee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L176-L177

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

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : 0 ≤ gaussNorm v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_nonneg» := P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee
