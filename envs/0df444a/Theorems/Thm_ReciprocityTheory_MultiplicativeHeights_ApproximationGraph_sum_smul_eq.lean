-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_sum_smul_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_smul_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:12.80273+00:00
-- url     : https://prove2.me/theorems/901c1f0f-3f5a-4bb4-8249-e6708b7e1b1d
-- title:
--   Approximation Graph: sum smul eq
-- statement:
--   The Approximation Graph construction uses the sum smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L137-L143

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_smul_eq {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) (c : ℂ) :
    ∑ j, w j • X j = c • w + ∑ j, w j • (X j - c • (Pi.single j 1 : Fin r → ℂ)) := by sorry
