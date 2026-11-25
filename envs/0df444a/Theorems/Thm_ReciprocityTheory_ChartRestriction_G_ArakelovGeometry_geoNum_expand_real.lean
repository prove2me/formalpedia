-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_expand_real
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_expand_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:32.622076+00:00
-- url     : https://prove2.me/theorems/30b1c361-e019-4e76-be44-f370c7220275
-- title:
--   Arakelov Geometry: geo Num expand real
-- statement:
--   The Arakelov Geometry construction uses the geo Num expand real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L199-L204

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_expand_real (n : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt n V) (v : Fin n → K → ℤ) :
    (geoNum n V v : ℝ) =
      ∑ r : Fin n → K, (∏ i, (v i (r i) : ℝ)) * (geoNum n V (fun i => uv (r i)) : ℝ) := by sorry
