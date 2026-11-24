-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
-- name    : P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:59.340801+00:00
-- url     : https://prove2.me/theorems/6e722606-c619-4f5a-ae12-bdf48ae6667e
-- title:
--   P2 M Ground Theory Heights  Heights finsum log gauss Norm mul 2d474f4b01c5: P2 M Ground Theory Heights  Heights finsum log gauss Norm mul 2d474f4b01c5
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum log gauss Norm mul 2d474f4b01c5 construction uses the P2 M Ground Theory Heights  Heights finsum log gauss Norm mul 2d474f4b01c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussSum.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussSum.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
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

theorem P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5 {ι : Type*} {f g : MvPolynomial ι K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (f * g)) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_log_gaussNorm_mul» := P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
