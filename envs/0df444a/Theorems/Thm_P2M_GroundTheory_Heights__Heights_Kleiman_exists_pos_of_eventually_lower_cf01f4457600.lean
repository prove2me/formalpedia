-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:46.548547+00:00
-- url     : https://prove2.me/theorems/f92b2120-2326-59c5-ab91-62d6803d7b89
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists pos of eventually lower cf01f4457600: P2 M Ground Theory Heights  Heights Kleiman exists pos of eventually lower cf01f4457600
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists pos of eventually lower cf01f4457600 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists pos of eventually lower cf01f4457600 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L14-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600 {d : ℕ} {A : ℤ} (hA : 0 < A) {C : ℝ} {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n)
    (D : ℕ) (hD : 0 < D) : ∃ n₁ : ℕ, 0 < n₁ ∧ 0 < f (D * n₁) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_pos_of_eventually_lower» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600
