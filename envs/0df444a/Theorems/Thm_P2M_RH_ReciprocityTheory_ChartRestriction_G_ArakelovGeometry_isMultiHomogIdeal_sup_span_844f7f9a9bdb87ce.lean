-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce
-- name    : P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:26.207106+00:00
-- url     : https://prove2.me/theorems/49e84115-31ef-4402-b36f-42f6c999514b
-- title:
--   P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog Ideal sup span 844f7f9a9bdb87ce: P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog Ideal s
-- statement:
--   The P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog Ideal sup span 844f7f9a9bdb87ce construction uses the P2 M RH Reciprocity Theory Chart Restriction G Arakelov Geometry is Multi Homog Ideal sup span 844f7f9a9bdb87ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L215-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean#L215-L222

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

theorem P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (F ⊔ Ideal.span {f}) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«isMultiHomogIdeal_sup_span» := P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce
