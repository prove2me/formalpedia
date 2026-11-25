-- Prove2me | Theorems.Thm_PositivityTheory_RL_Delta_exists_div
-- name    : PositivityTheory.RL.Delta.exists_div
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:43.69999+00:00
-- url     : https://prove2.me/theorems/0fe95cea-1c32-42d5-ae87-a5459643d3fb
-- title:
--   Delta: exists div
-- statement:
--   The Delta construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L200-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L200-L244

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff

theorem PositivityTheory.RL.Delta.exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by sorry
