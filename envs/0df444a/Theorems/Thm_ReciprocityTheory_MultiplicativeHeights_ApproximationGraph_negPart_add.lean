-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negPart_add
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.negPart_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:47.439276+00:00
-- url     : https://prove2.me/theorems/ec88e759-560c-476a-b9db-79eefb6f276f
-- title:
--   Approximation Graph: neg Part add
-- statement:
--   The Approximation Graph construction uses the neg Part add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L54-L58

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by sorry
