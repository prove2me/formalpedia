-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_entire_poly_of_growth
-- name    : ReciprocityTheory.MultiplicativeHeights.entire_poly_of_growth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:14.432455+00:00
-- url     : https://prove2.me/theorems/cb93a949-cb90-40d7-870b-fcb54388a1b9
-- title:
--   Multiplicative Heights: entire poly of growth
-- statement:
--   The Multiplicative Heights construction uses the entire poly of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/OnePolyGrowth.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/OnePolyGrowth.lean#L8-L11

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Lemmata_IterateZero_IterZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_OnePolyGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Filter Topology Function Metric Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.entire_poly_of_growth (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by sorry
