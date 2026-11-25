-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_prod_pow_sub
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.prod_pow_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:47.649627+00:00
-- url     : https://prove2.me/theorems/1aa6478d-e6ff-43a1-898f-72f1120541be
-- title:
--   Div LA: prod pow sub
-- statement:
--   The Div LA construction uses the prod pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L49-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L49-L67

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.prod_pow_sub {ι : Type*} (s : Finset ι) (u v : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) (hv : ∀ i, v i =O[𝓝 0] fun z => ‖z‖)
    (huv : ∀ i, (fun z => u i z - v i z) =O[𝓝 0] fun z => ‖z‖ ^ 2) :
    (fun z => ∏ i ∈ s, u i z ^ e i - ∏ i ∈ s, v i z ^ e i) =O[𝓝 0]
      fun z => ‖z‖ ^ (∑ i ∈ s, e i + 1) := by sorry
