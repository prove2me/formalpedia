-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:44.2898+00:00
-- url     : https://prove2.me/theorems/d578a8dc-ccee-57f7-9b6c-786e47f26385
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Halving eventually le 124ebeeb4013: P2 M Ground Theory Heights  Heights Hilbert Samuel Halving eventually le 124ebeeb4013
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Halving eventually le 124ebeeb4013 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Halving eventually le 124ebeeb4013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHalving.lean#L9-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHalving.lean#L9-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHalving
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
open Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013 (a : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |a n| ≤ C)
    (hh : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0))
    (hs : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)) (k : ℕ) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| ≤ C / 2 ^ k + ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«Halving».«eventually_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013
