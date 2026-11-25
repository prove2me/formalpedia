-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:49.668869+00:00
-- url     : https://prove2.me/theorems/388b9d3c-9b52-4abf-8231-6522917e57d0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists separating b05fbc61f580: P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists separating
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists separating b05fbc61f580 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Finite Separating Model exists separating b05fbc61f580 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L67-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiniteSeparatingModel.lean#L67-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
variable {σ : Type} {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580 [Fintype σ] (S : Finset (σ → ℂ)) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℚ, ∀ z ∈ S, aeval z u = aeval x u → z = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiniteSeparatingModel».«exists_separating» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580
