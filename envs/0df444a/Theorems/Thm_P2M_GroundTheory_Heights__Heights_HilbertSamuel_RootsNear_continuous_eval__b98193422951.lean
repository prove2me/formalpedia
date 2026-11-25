-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:29.074993+00:00
-- url     : https://prove2.me/theorems/bac58679-b747-484b-ad28-768c8c401f5c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near continuous eval  b98193422951: P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near continuous eval  b98193422951
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near continuous eval  b98193422951 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near continuous eval  b98193422951 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsNear.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsNear.lean#L21-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsNear
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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951 {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootsNear».«continuous_eval₂» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_continuous_eval__b98193422951
