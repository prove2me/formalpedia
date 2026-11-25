-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_prod_update_split
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_update_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:12.123093+00:00
-- url     : https://prove2.me/theorems/c2b281bf-d6d5-4b42-91d1-9bb1592d44da
-- title:
--   Arakelov Geometry: prod update split
-- statement:
--   The Arakelov Geometry construction uses the prod update split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L105-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L105-L120

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.prod_update_split {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∏ j, Function.update g i t j = t * (∏ j with j < i, g j) * ∏ j with i < j, g j := by sorry
