-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_graphMap_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.graphMap_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:17.319233+00:00
-- url     : https://prove2.me/theorems/29f35052-6235-5e34-9c3a-bbaf22e700ea
-- title:
--   Approximation Graph: graph Map apply
-- statement:
--   The Approximation Graph construction uses the graph Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphB.lean#L131-L132

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.graphMap_apply (p : ℕ) {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    graphMap p X w = posPart p (∑ j, posPart p w j • X j) + negPart p w := by sorry
