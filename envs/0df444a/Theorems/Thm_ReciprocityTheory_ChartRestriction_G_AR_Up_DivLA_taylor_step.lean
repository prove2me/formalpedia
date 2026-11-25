-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_taylor_step
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.taylor_step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:20.850421+00:00
-- url     : https://prove2.me/theorems/f2e13b0a-3698-5ebf-872f-2da9d5641339
-- title:
--   Div LA: taylor step
-- statement:
--   The Div LA construction uses the taylor step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L34-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L34-L86

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.taylor_step {n d : ℕ} {G : V n → ℂ} (hG : AnalyticAt ℂ G 0)
    (hO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ,
      (fun z => G z - q (fun _ => z)) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by sorry
