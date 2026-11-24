-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_normSq__0_diag_d4b194bb0a12
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_normSq__0_diag_d4b194bb0a12
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:46.646935+00:00
-- url     : https://prove2.me/theorems/98d19eb6-8a85-49d7-b952-03a62470a2c7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI norm Sq  0 diag d4b194bb0a12: P2 M Reciprocity Theory Chart Restriction G AR Up MI norm Sq  0 diag d4b194bb0a12
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI norm Sq  0 diag d4b194bb0a12 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI norm Sq  0 diag d4b194bb0a12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfJ.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfJ.lean#L49-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_normSq__0_diag_d4b194bb0a12 {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«normSq_β0_diag» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_normSq__0_diag_d4b194bb0a12
