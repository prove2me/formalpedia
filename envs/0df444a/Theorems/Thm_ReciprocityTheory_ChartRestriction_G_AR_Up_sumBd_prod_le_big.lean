-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_prod_le_big
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_prod_le_big
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:59.110108+00:00
-- url     : https://prove2.me/theorems/cf5dac89-c673-5e92-8093-103f8e8d2dba
-- title:
--   Up: sum Bd prod le big
-- statement:
--   The Up construction uses the sum Bd prod le big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L53-L58

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_prod_le_big {f : ℕ} (w : Fin f → ℝ) (h0 : ∀ k, 0 ≤ w k) (h1 : ∀ k, w k ≤ 1) (k0 : Fin f)
    {b : ℝ} (hb : w k0 ≤ b) : ∏ k, w k ≤ b := by sorry
