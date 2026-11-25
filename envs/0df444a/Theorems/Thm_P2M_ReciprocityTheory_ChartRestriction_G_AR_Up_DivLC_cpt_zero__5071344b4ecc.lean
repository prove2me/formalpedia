-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_cpt_zero__5071344b4ecc
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_cpt_zero__5071344b4ecc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:24.063857+00:00
-- url     : https://prove2.me/theorems/5d1f9ff0-e810-44c8-94a3-ac8549131421
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Div LC cpt zero  5071344b4ecc: P2 M Reciprocity Theory Chart Restriction G AR Up Div LC cpt zero  5071344b4ecc
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Div LC cpt zero  5071344b4ecc construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Div LC cpt zero  5071344b4ecc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLC.lean#L26-L30

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_cpt_zero__5071344b4ecc (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«DivLC».«cpt_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_cpt_zero__5071344b4ecc
