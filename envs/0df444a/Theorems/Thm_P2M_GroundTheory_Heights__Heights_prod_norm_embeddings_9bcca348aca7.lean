-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7
-- name    : P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:37.532458+00:00
-- url     : https://prove2.me/theorems/5054c609-4f63-490a-bb6b-df5a8d704d13
-- title:
--   P2 M Ground Theory Heights  Heights prod norm embeddings 9bcca348aca7: P2 M Ground Theory Heights  Heights prod norm embeddings 9bcca348aca7
-- statement:
--   The P2 M Ground Theory Heights  Heights prod norm embeddings 9bcca348aca7 construction uses the P2 M Ground Theory Heights  Heights prod norm embeddings 9bcca348aca7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L97-L103

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

theorem P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7 (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«prod_norm_embeddings» := P2M_GroundTheory_Heights__Heights_prod_norm_embeddings_9bcca348aca7
