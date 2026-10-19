-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_exists_avoiding_finite_smooth_chart_images
-- name    : PermanentRollout.permanent_rollout_exists_avoiding_finite_smooth_chart_images
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/c28b99d3-154a-41aa-be94-ec518816f037
-- title:
--   PermanentRollout.permanent_rollout_exists_avoiding_finite_smooth_chart_images
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section

theorem PermanentRollout.permanent_rollout_exists_avoiding_finite_smooth_chart_images
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : ι → E → F) (s : ι → Set E)
    (hsmooth : ∀ i x, x ∈ s i → ContDiffAt ℝ 1 (f i) x)
    (hdim : finrank ℝ E < finrank ℝ F) :
    ∃ y : F, ∀ i : ι, y ∉ f i '' s i := by sorry
