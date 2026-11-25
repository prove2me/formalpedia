-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_single_mem_periods_084bea907d50
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_single_mem_periods_084bea907d50
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:44.30059+00:00
-- url     : https://prove2.me/theorems/c92c1768-dc9d-4fa0-a1c3-777887e9327f
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent single mem periods 084bea907d50: P2 M Ground Theory Heights  Heights Regular Log Cover Descent single mem periods 084bea907d50
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent single mem periods 084bea907d50 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent single mem periods 084bea907d50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L50-L62

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

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_single_mem_periods_084bea907d50 {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w)
    (k : Fin n) (hk : k.val < a) : Pi.single k (2 * Real.pi * Complex.I) ∈ periods h φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«single_mem_periods» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_single_mem_periods_084bea907d50
