-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94
-- name    : P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:11.862823+00:00
-- url     : https://prove2.me/theorems/8728be70-24bd-4f7a-838f-9c6fa90252f3
-- title:
--   P2 M Ground Theory Heights  Heights Section Injectivity chart Form mul pow 64b836c95b94: P2 M Ground Theory Heights  Heights Section Injectivity chart Form mul pow 64b836c95b94
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Injectivity chart Form mul pow 64b836c95b94 construction uses the P2 M Ground Theory Heights  Heights Section Injectivity chart Form mul pow 64b836c95b94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroMore.lean#L40-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false

theorem P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94 {P : ArithVariety n} {num₁ den₁ num₂ den₂ : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d₁ d₂ : ι → ℕ} {f₁ f₂ : MvPolynomial (Coord n) ℤ} (t : ℕ)
    (h₁ : den₁ * f₁ - num₁ * chartMonomial c d₁ ∈ P.ideal)
    (h₂ : den₂ * f₂ - num₂ * chartMonomial c d₂ ∈ P.ideal) :
    den₁ * den₂ ^ t * (f₁ * f₂ ^ t) - num₁ * num₂ ^ t * chartMonomial c (d₁ + t • d₂) ∈ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionInjectivity».«chartForm_mul_pow» := P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94
