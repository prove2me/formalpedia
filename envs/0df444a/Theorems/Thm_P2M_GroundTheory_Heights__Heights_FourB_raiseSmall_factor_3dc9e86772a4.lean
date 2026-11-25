-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4
-- name    : P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:43.022291+00:00
-- url     : https://prove2.me/theorems/260be54c-7b00-47d7-ae1c-3420f7a79baa
-- title:
--   P2 M Ground Theory Heights  Heights Four B raise Small factor 3dc9e86772a4: P2 M Ground Theory Heights  Heights Four B raise Small factor 3dc9e86772a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B raise Small factor 3dc9e86772a4 construction uses the P2 M Ground Theory Heights  Heights Four B raise Small factor 3dc9e86772a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PDegreeRatio.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PDegreeRatio.lean#L22-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PDegreeRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB

theorem P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4 {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ)
    (hx : ∀ τ (i l : Fin N), i < l → x τ l < x τ i) (τ : Fin f) (i l : Fin N) :
    (if i < l then raiseSmall N j' δ x τ i - raiseSmall N j' δ x τ l else 1) =
      (if i < l then x τ i - x τ l else 1) *
        (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«raiseSmall_factor» := P2M_GroundTheory_Heights__Heights_FourB_raiseSmall_factor_3dc9e86772a4
