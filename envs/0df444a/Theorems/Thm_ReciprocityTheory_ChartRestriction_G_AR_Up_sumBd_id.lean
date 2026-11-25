-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_id
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_id
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:50.55781+00:00
-- url     : https://prove2.me/theorems/2b1a708d-5ddd-4a9f-8855-6c9dfd5f28db
-- title:
--   Up: sum Bd id
-- statement:
--   The Up construction uses the sum Bd id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L12-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_id (A0 B s : ℝ) (N j : ℕ) (hB : 0 ≤ B) :
    (A0 * ((2 : ℝ) ^ j) ^ 2) ^ N * (B / 4 ^ j) ^ s = A0 ^ N * B ^ s * ((4 : ℝ) ^ N / 4 ^ s) ^ j := by sorry
