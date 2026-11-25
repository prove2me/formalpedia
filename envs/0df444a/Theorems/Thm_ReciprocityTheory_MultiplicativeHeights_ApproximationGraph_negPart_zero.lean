-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.negPart_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:12.281031+00:00
-- url     : https://prove2.me/theorems/5f3396a5-1a88-5e49-bb45-b5a651d12c85
-- title:
--   Approximation Graph: neg Part zero
-- statement:
--   The Approximation Graph construction uses the neg Part zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L33-L35

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.negPart_zero (p : ℕ) {r : ℕ} : negPart p (0 : Fin r → ℂ) = 0 := by sorry
