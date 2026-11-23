-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_mul__4b7051dfc546
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_mul__4b7051dfc546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:30.881404+00:00
-- url     : https://prove2.me/theorems/0cf88a15-0195-43ea-8e6f-d95304e009e3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Div St sec mul  4b7051dfc546: P2 M Reciprocity Theory Chart Restriction G AR Up Div St sec mul  4b7051dfc546
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Div St sec mul  4b7051dfc546 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Div St sec mul  4b7051dfc546 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L35-L37

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_mul__4b7051dfc546 {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hQ : X.IsSec la' Q) :
    X.IsSec (la + la') (fun x => P x * Q x) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«DivSt».«sec_mul'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_mul__4b7051dfc546
