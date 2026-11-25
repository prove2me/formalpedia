-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_sub_prod_sub_lin_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_sub_prod_sub_lin_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:44.764467+00:00
-- url     : https://prove2.me/theorems/7a383def-e1a8-48a8-9c09-bc2edb944979
-- title:
--   Arakelov Geometry: abs prod sub prod sub lin le
-- statement:
--   The Arakelov Geometry construction uses the abs prod sub prod sub lin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L62-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L62-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_sub_prod_sub_lin_le {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) -
        ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| ≤
      s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by sorry
