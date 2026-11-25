-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_comp_O
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.comp_O
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:31.729486+00:00
-- url     : https://prove2.me/theorems/fa4edd40-d3f8-4e10-82b0-dec942bd64f9
-- title:
--   Div LA: comp O
-- statement:
--   The Div LA construction uses the comp O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLD.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLD.lean#L11-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLD
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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by sorry
