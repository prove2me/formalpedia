-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_sub_le__9a0fedfcc007
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_sub_le__9a0fedfcc007
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:07.598981+00:00
-- url     : https://prove2.me/theorems/1e6afb63-10a5-56b5-94fb-23963ab4bbd4
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Div St pnorm sub le  9a0fedfcc007: P2 M Reciprocity Theory Chart Restriction G AR Up Div St pnorm sub le  9a0fedfcc007
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Div St pnorm sub le  9a0fedfcc007 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Div St pnorm sub le  9a0fedfcc007 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L198-L201

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_sub_le__9a0fedfcc007 (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«DivSt».«pnorm_sub_le'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_pnorm_sub_le__9a0fedfcc007
