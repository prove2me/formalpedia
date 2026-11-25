-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_isBigO_norm_pow_of_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.isBigO_norm_pow_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:02.268588+00:00
-- url     : https://prove2.me/theorems/db8de36b-1143-4bde-aaf8-3eb8aea54d92
-- title:
--   Div LA: is Big O norm pow of le
-- statement:
--   The Div LA construction uses the is Big O norm pow of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L26-L32

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.isBigO_norm_pow_of_le {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by sorry
