-- Prove2me | Theorems.Thm_PositivityTheory_RL_Delta_dense_hasCompactSupport
-- name    : PositivityTheory.RL.Delta.dense_hasCompactSupport
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:00.623386+00:00
-- url     : https://prove2.me/theorems/8b2be944-ef94-4afe-b4a5-0b45c1a800f3
-- title:
--   Delta: dense has Compact Support
-- statement:
--   The Delta construction uses the dense has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L72-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean#L72-L162

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

theorem PositivityTheory.RL.Delta.dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by sorry
