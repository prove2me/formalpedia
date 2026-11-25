-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prod_monomial__b38161db3b9b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prod_monomial__b38161db3b9b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:14.126828+00:00
-- url     : https://prove2.me/theorems/5c1c6247-100a-495c-922a-3cca668d0d11
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols prod monomial  b38161db3b9b: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols prod monomial  b38161db3b9b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols prod monomial  b38161db3b9b construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols prod monomial  b38161db3b9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaHCols.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaHCols.lean#L82-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prod_monomial__b38161db3b9b {β : Type} (s : Finset β) (g : β → ι × Fin n →₀ ℕ) (a : β → k) :
    ∏ b ∈ s, monomial (g b) (a b) = monomial (∑ b ∈ s, g b) (∏ b ∈ s, a b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«HCols».«prod_monomial'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prod_monomial__b38161db3b9b
