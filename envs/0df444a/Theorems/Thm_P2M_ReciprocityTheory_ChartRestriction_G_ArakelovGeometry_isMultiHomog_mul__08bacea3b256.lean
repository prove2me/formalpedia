-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul__08bacea3b256
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul__08bacea3b256
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:12.937221+00:00
-- url     : https://prove2.me/theorems/07364d99-2e55-519c-b4f8-24abc29a33d1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog mul  08bacea3b256: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog mul  08bacea3b256
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog mul  08bacea3b256 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog mul  08bacea3b256 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L115-L123

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul__08bacea3b256 {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«isMultiHomog_mul'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul__08bacea3b256
