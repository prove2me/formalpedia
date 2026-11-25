-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_update_eq_snoc
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_update_eq_snoc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:09:36.570735+00:00
-- url     : https://prove2.me/theorems/1a4f43f2-3fb1-5162-a746-a1f836b1329f
-- title:
--   Arakelov Geometry: geo Num update eq snoc
-- statement:
--   The Arakelov Geometry construction uses the geo Num update eq snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L221-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AbsProdSubProdSubLinLe.lean#L221-L230

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_update_eq_snoc (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x e : K → ℤ)
    (i : Fin (m + 1)) :
    geoNum (m + 1) V (Function.update (fun _ => x) i e) = geoNum (m + 1) V (Fin.snoc (fun _ => x) e) := by sorry
