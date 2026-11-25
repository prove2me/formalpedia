-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TubeSummability_summable_exp_abs
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TubeSummability.summable_exp_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:28.050039+00:00
-- url     : https://prove2.me/theorems/ca424b3f-3326-4135-85bd-6c62fe979ef4
-- title:
--   Tube Summability: summable exp abs
-- statement:
--   The Tube Summability construction uses the summable exp abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeSummability.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeSummability.lean#L12-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate

theorem ReciprocityTheory.ChartRestriction.G.FD.TubeSummability.summable_exp_abs (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by sorry
