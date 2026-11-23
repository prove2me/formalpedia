-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:39.220827+00:00
-- url     : https://prove2.me/theorems/3437fa8e-1c9b-4b55-ae4a-7fad0591c582
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Div St nfac nonneg  30ef8672819a: P2 M Reciprocity Theory Chart Restriction G AR Up Div St nfac nonneg  30ef8672819a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Div St nfac nonneg  30ef8672819a construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Div St nfac nonneg  30ef8672819a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L112-L113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«DivSt».«nfac_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_nfac_nonneg__30ef8672819a
