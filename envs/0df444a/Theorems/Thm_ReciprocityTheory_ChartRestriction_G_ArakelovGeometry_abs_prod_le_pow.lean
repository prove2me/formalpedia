-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_le_pow
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_le_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:45.976786+00:00
-- url     : https://prove2.me/theorems/2ac623ad-68f2-4208-b236-bf2bdd29fa8e
-- title:
--   Arakelov Geometry: abs prod le pow
-- statement:
--   The Arakelov Geometry construction uses the abs prod le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L11-L15

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_le_pow {α : Type*} (s : Finset α) (y : α → ℝ) {Y : ℝ} (hy : ∀ i ∈ s, |y i| ≤ Y) :
    |∏ i ∈ s, y i| ≤ Y ^ s.card := by sorry
