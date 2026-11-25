-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_pow_sub_pow
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.pow_sub_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:08.215216+00:00
-- url     : https://prove2.me/theorems/afacd2bc-9750-5cca-b9e9-a4a22642b2b5
-- title:
--   Div LA: pow sub pow
-- statement:
--   The Div LA construction uses the pow sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L17-L36

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.pow_sub_pow {u v : V n → ℂ} (hu : u =O[𝓝 0] fun z => ‖z‖) (hv : v =O[𝓝 0] fun z => ‖z‖)
    (huv : (fun z => u z - v z) =O[𝓝 0] fun z => ‖z‖ ^ 2) (e : ℕ) :
    (fun z => u z ^ e - v z ^ e) =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by sorry
