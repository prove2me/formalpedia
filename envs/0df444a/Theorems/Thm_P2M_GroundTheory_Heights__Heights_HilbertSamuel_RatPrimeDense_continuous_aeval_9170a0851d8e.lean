-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:57.764616+00:00
-- url     : https://prove2.me/theorems/053d142b-46e5-43f6-b036-50345289e75e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Rat Prime Dense continuous aeval 9170a0851d8e: P2 M Ground Theory Heights  Heights Hilbert Samuel Rat Prime Dense continuous aeval 9170a0851d8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Rat Prime Dense continuous aeval 9170a0851d8e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Rat Prime Dense continuous aeval 9170a0851d8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRatPrimeDense.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRatPrimeDense.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRatPrimeDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonvanishDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRatPrimeDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e {σ : Type} (g : MvPolynomial σ ℚ) :
    Continuous fun z : σ → ℂ => aeval z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RatPrimeDense».«continuous_aeval» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RatPrimeDense_continuous_aeval_9170a0851d8e
