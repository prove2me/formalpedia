-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_mulO
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.mulO
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:07.336981+00:00
-- url     : https://prove2.me/theorems/28a7c365-c32a-494d-809a-5fc8b76dabc5
-- title:
--   Div LA: mul O
-- statement:
--   The Div LA construction uses the mul O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L11-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.mulO {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by sorry
