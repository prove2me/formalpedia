-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f
-- name    : P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:51.371201+00:00
-- url     : https://prove2.me/theorems/4c3d4d8e-09a5-4e22-8575-13cb2f57ea13
-- title:
--   P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry mem m Hom iff eb27d564b98b5c3f: P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry mem m Hom iff eb27d564b98b5c3f
-- statement:
--   The P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry mem m Hom iff eb27d564b98b5c3f construction uses the P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry mem m Hom iff eb27d564b98b5c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L93-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L93-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f (s : MRing ι) (a : K → ℕ) : s ∈ mHom ι a ↔ IsMultiHomog s a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«mem_mHom_iff» := P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff_eb27d564b98b5c3f
