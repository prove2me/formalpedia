-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b
-- name    : P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:32.066652+00:00
-- url     : https://prove2.me/theorems/1b73a1e3-832a-5eed-871e-63868fbb3829
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Lie Last transport small Power Sum 8cdf674c2e5b: P2 M Ground Theory Heights  Heights Rest Cut Lie Last transport small Power Sum 8cdf674c2e5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Lie Last transport small Power Sum 8cdf674c2e5b construction uses the P2 M Ground Theory Heights  Heights Rest Cut Lie Last transport small Power Sum 8cdf674c2e5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutLieLast.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutLieLast.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieLast
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
open GroundTheory.Heights₂.Heights.RestCutLieLast

theorem P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallPowerSum f k j .last m τ) =
      ∑ b : Fin k, X (τ, Sum.inr b) ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutLieLast».«transport_smallPowerSum» := P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b
