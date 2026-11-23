-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_normSq_eq_euc
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.normSq_eq_euc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:57.194458+00:00
-- url     : https://prove2.me/theorems/112a7ac6-ac27-40a9-b5be-71d2f7d7419e
-- title:
--   Approximation Graph: norm Sq eq euc
-- statement:
--   The Approximation Graph construction uses the norm Sq eq euc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L19-L21

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by sorry
