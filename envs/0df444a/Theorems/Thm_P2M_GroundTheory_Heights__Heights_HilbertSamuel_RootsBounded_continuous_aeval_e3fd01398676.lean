-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:17.356367+00:00
-- url     : https://prove2.me/theorems/44093ed4-fa18-4e4e-8abe-339de09542e3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Bounded continuous aeval e3fd01398676: P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Bounded continuous aeval e3fd01398676
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Bounded continuous aeval e3fd01398676 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Bounded continuous aeval e3fd01398676 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsBounded.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsBounded.lean#L9-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsBounded
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
open MvPolynomial Filter Topology NNReal

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676 {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootsBounded».«continuous_aeval» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676
