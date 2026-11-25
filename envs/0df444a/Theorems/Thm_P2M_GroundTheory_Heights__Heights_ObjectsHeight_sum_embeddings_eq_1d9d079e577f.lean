-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:06.856128+00:00
-- url     : https://prove2.me/theorems/adc4d2c7-6002-4123-b113-9e63d7c03bc9
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height sum embeddings eq 1d9d079e577f: P2 M Ground Theory Heights  Heights Objects Height sum embeddings eq 1d9d079e577f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height sum embeddings eq 1d9d079e577f construction uses the P2 M Ground Theory Heights  Heights Objects Height sum embeddings eq 1d9d079e577f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L465-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L465-L478

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f {K : Type*} [Field K] [NumberField K] (F : (K →+* ℂ) → ℝ)
    (hF : ∀ σ, F (ComplexEmbedding.conjugate σ) = F σ) :
    ∑ σ, F σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * F w.embedding := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«sum_embeddings_eq» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_sum_embeddings_eq_1d9d079e577f
