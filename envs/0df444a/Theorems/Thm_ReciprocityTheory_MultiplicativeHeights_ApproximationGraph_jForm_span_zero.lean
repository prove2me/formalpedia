-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_span_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_span_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:34.294277+00:00
-- url     : https://prove2.me/theorems/9a91dc51-e0b2-4ff7-9466-f6d6b6125a81
-- title:
--   Approximation Graph: j Form span zero
-- statement:
--   The Approximation Graph construction uses the j Form span zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L28-L36

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphC
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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_span_zero (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (y : Fin r → ℂ)
    (hy : ∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) (w : Fin r → ℂ)
    (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) : jForm p (∑ j, w j • X j) y = 0 := by sorry
