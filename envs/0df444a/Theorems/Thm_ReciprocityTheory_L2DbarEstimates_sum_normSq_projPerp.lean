-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sum_normSq_projPerp
-- name    : ReciprocityTheory.L2DbarEstimates.sum_normSq_projPerp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:25.275433+00:00
-- url     : https://prove2.me/theorems/9ce78949-1449-4d6d-94c4-edc33ab9f9dd
-- title:
--   L2 Dbar Estimates: sum norm Sq proj Perp
-- statement:
--   The L2 Dbar Estimates construction uses the sum norm Sq proj Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L96-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.sum_normSq_projPerp {g : Fin p → ℂ} (hg : g ≠ 0) :
    ∑ i, ∑ l, Complex.normSq (projPerp g i l) = (p : ℝ) - 1 := by sorry
