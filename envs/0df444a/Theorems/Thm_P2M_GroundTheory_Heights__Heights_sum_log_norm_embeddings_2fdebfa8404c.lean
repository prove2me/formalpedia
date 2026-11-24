-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c
-- name    : P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:31.424859+00:00
-- url     : https://prove2.me/theorems/d0c42a9a-b84b-4916-903b-34a212b1ec32
-- title:
--   P2 M Ground Theory Heights  Heights sum log norm embeddings 2fdebfa8404c: P2 M Ground Theory Heights  Heights sum log norm embeddings 2fdebfa8404c
-- statement:
--   The P2 M Ground Theory Heights  Heights sum log norm embeddings 2fdebfa8404c construction uses the P2 M Ground Theory Heights  Heights sum log norm embeddings 2fdebfa8404c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L105-L109

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

theorem P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c {x : K} (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_log_norm_embeddings» := P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c
