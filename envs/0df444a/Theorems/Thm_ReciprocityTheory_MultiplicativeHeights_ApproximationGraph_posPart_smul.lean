-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_posPart_smul
-- name    : ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:39.609138+00:00
-- url     : https://prove2.me/theorems/76b52067-8ef0-472c-859d-75e507d2310a
-- title:
--   Approximation Graph: pos Part smul
-- statement:
--   The Approximation Graph construction uses the pos Part smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean#L60-L64

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

theorem ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by sorry
