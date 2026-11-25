-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_constants_le_910cce236f40
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_constants_le_910cce236f40
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:40.46107+00:00
-- url     : https://prove2.me/theorems/9138e747-ddda-4586-a954-6394466a1917
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS lift constants le 910cce236f40: P2 M Ground Theory Heights  Heights Effective HS lift constants le 910cce236f40
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS lift constants le 910cce236f40 construction uses the P2 M Ground Theory Heights  Heights Effective HS lift constants le 910cce236f40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L213-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L213-L249

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open Real

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_constants_le_910cce236f40 (D : ℕ) (hD : 1 ≤ D) (ρ ρ₁ T C : ℝ) (hρ : 2 ^ 26 ≤ ρ)
    (hDρ : (D : ℝ) ≤ ρ) (h1 : 1 ≤ ρ₁) (h1ρ : ρ₁ ≤ ρ) (hT : 1 ≤ T) (hC : 26 ≤ C) :
    2 * D * log ρ₁ + D * log (Real.sqrt D * ρ₁) + (1 / 2) * log (140 * cD D * T ^ D) ≤
        4 * D * log (ρ * T) ∧
      4 * D * log (ρ * T) ≤ C * D ^ 2 * log (ρ * T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«lift_constants_le» := P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_constants_le_910cce236f40
