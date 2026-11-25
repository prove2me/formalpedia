-- Prove2me | Theorems.Thm_PositivityTheory_RL_Delta_zero_of_ball
-- name    : PositivityTheory.RL.Delta.zero_of_ball
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:56.953098+00:00
-- url     : https://prove2.me/theorems/03481c17-4f99-497a-8e93-703add74080c
-- title:
--   Delta: zero of ball
-- statement:
--   The Delta construction uses the zero of ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L246-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L246-L264

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

theorem PositivityTheory.RL.Delta.zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by sorry
