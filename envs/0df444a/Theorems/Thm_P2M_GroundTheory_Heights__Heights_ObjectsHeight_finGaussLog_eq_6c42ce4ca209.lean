-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:56.593127+00:00
-- url     : https://prove2.me/theorems/a6e82e44-16b9-49f7-8b82-9e52747b162c
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height fin Gauss Log eq 6c42ce4ca209: P2 M Ground Theory Heights  Heights Objects Height fin Gauss Log eq 6c42ce4ca209
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height fin Gauss Log eq 6c42ce4ca209 construction uses the P2 M Ground Theory Heights  Heights Objects Height fin Gauss Log eq 6c42ce4ca209 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L367-L370

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209 {ι : Type*} (f : MvPolynomial ι ℚ) :
    IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«finGaussLog_eq» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209
