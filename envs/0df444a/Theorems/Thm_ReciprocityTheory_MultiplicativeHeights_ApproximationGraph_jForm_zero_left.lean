-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_zero_left
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_zero_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:04.286389+00:00
-- url     : https://prove2.me/theorems/c7f84ffd-4a98-4252-b775-ee58e10cac6a
-- title:
--   Approximation Graph: j Form zero left
-- statement:
--   The Approximation Graph construction uses the j Form zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L9-L10

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_zero_left (p : ℕ) {r : ℕ} (y : Fin r → ℂ) : jForm p 0 y = 0 := by sorry
