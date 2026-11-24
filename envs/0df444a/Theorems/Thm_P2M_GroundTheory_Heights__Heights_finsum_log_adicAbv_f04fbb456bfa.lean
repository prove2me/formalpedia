-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
-- name    : P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:55.145819+00:00
-- url     : https://prove2.me/theorems/62481788-1aec-4c98-9cfa-50aa6d796af1
-- title:
--   P2 M Ground Theory Heights  Heights finsum log adic Abv f04fbb456bfa: P2 M Ground Theory Heights  Heights finsum log adic Abv f04fbb456bfa
-- statement:
--   The P2 M Ground Theory Heights  Heights finsum log adic Abv f04fbb456bfa construction uses the P2 M Ground Theory Heights  Heights finsum log adic Abv f04fbb456bfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L111-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L111-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v x) =
        -Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finsum_log_adicAbv» := P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
