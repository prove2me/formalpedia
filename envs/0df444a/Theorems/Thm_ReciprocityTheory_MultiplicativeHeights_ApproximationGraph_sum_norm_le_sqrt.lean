-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_sum_norm_le_sqrt
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_norm_le_sqrt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:45.869636+00:00
-- url     : https://prove2.me/theorems/b290f7ad-15f9-4ed2-82b5-a1c2bee4f743
-- title:
--   Approximation Graph: sum norm le sqrt
-- statement:
--   The Approximation Graph construction uses the sum norm le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L132-L135

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by sorry
