-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_nmat_zero__bcf4e49f5f2b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_nmat_zero__bcf4e49f5f2b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:59.936803+00:00
-- url     : https://prove2.me/theorems/f70c9d70-c98e-4670-ac86-54a2ff960a40
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Div LC nmat zero  bcf4e49f5f2b: P2 M Reciprocity Theory Chart Restriction G AR Up Div LC nmat zero  bcf4e49f5f2b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Div LC nmat zero  bcf4e49f5f2b construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Div LC nmat zero  bcf4e49f5f2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L16-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_nmat_zero__bcf4e49f5f2b (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«DivLC».«nmat_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_nmat_zero__bcf4e49f5f2b
