-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_prod_pow_O
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.prod_pow_O
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:13.75239+00:00
-- url     : https://prove2.me/theorems/296f3282-0dbf-56e3-a5ca-65100fa600e8
-- title:
--   Div LA: prod pow O
-- statement:
--   The Div LA construction uses the prod pow O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLB.lean#L38-L47

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.prod_pow_O {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by sorry
