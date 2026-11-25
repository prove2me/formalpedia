-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844
-- name    : P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:19.774689+00:00
-- url     : https://prove2.me/theorems/18107493-52fa-4c29-b41c-a4516094116f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Lie First transport small Power Sum 9e1dd0b87844: P2 M Ground Theory Heights  Heights Rest Cut Lie First transport small Power Sum 9e1dd0b87844
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Lie First transport small Power Sum 9e1dd0b87844 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Lie First transport small Power Sum 9e1dd0b87844 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutLieFirst.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutLieFirst.lean#L13-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieFirst
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
open GroundTheory.Heights₂.Heights.RestCutLieFirst

theorem P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844 (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallPowerSum f j k .first m τ) =
      (-1) ^ m * ∑ a : Fin j, (X (τ, Sum.inl a) : RootPoly f j k) ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutLieFirst».«transport_smallPowerSum» := P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844
