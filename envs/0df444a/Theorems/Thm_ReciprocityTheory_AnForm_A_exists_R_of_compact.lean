-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_exists_R_of_compact
-- name    : ReciprocityTheory.AnForm.A.exists_R_of_compact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:10.429931+00:00
-- url     : https://prove2.me/theorems/46209076-4b10-4df8-9cfe-34e84466d249
-- title:
--   A: exists R of compact
-- statement:
--   The A construction uses the exists R of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LeviOneEqLaplacianThm.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LeviOneEqLaplacianThm.lean#L12-L18

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section

theorem ReciprocityTheory.AnForm.A.exists_R_of_compact {F : Type} [NormedAddCommGroup F] {u : F → ℝ}
    (hc : HasCompactSupport u) : ∃ R > 0, ∀ q, q ∈ tsupport u → ‖q‖ ≤ R := by sorry
