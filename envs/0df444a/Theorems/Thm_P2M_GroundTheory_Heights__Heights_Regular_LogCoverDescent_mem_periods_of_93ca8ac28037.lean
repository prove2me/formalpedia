-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_mem_periods_of_93ca8ac28037
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_mem_periods_of_93ca8ac28037
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:12.231913+00:00
-- url     : https://prove2.me/theorems/09928ade-5230-5108-8ad6-63871923e4c1
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent mem periods of 93ca8ac28037: P2 M Ground Theory Heights  Heights Regular Log Cover Descent mem periods of 93ca8ac28037
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent mem periods of 93ca8ac28037 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent mem periods of 93ca8ac28037 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L64-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_mem_periods_of_93ca8ac28037 {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {v : Fin n → ℂ}
    (hv : ∀ k : Fin n, (k.val < a → ∃ m : ℤ, v k = m * (2 * Real.pi * Complex.I)) ∧
      (a ≤ k.val → v k = 0)) :
    v ∈ periods h φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«mem_periods_of» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_mem_periods_of_93ca8ac28037
