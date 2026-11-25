-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_jForm_smul_left
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_smul_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:53.848772+00:00
-- url     : https://prove2.me/theorems/1d856323-cca6-43a5-8cd7-1fd5a2342ba0
-- title:
--   Approximation Graph: j Form smul left
-- statement:
--   The Approximation Graph construction uses the j Form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphC.lean#L16-L19

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_smul_left (p : ℕ) {r : ℕ} (c : ℂ) (x y : Fin r → ℂ) :
    jForm p (c • x) y = conj c * jForm p x y := by sorry
