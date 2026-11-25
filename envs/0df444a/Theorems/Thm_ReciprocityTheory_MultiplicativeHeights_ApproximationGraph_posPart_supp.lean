-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_supp
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_supp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:50.169084+00:00
-- url     : https://prove2.me/theorems/0277528a-b53f-4ae3-a410-a8c1be50e9bf
-- title:
--   Approximation Graph: pos Part supp
-- statement:
--   The Approximation Graph construction uses the pos Part supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L37-L38

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_supp (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ∀ j : Fin r, p ≤ (j : ℕ) → posPart p u j = 0 := by sorry
