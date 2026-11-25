-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_zero__6c5105cab79c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_zero__6c5105cab79c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:03:25.310466+00:00
-- url     : https://prove2.me/theorems/c18894d6-3a45-5072-ad15-446abb0f5297
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols iter zero  6c5105cab79c: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols iter zero  6c5105cab79c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols iter zero  6c5105cab79c construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing HCols iter zero  6c5105cab79c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaHCols.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaHCols.lean#L146-L149

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_zero__6c5105cab79c (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    (secondOrder k c)^[i] (0 : MvPolynomial (ι × Fin n) k) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«HCols».«iter_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_zero__6c5105cab79c
