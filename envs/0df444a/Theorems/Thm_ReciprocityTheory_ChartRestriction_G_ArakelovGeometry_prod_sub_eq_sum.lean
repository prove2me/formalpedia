-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_prod_sub_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_sub_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:48.16344+00:00
-- url     : https://prove2.me/theorems/50fe960c-7fc5-441a-9228-9a26ec46b1f3
-- title:
--   Arakelov Geometry: prod sub eq sum
-- statement:
--   The Arakelov Geometry construction uses the prod sub eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L28-L35

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_sub_eq_sum {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) :
    ∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) =
      ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j := by sorry
