-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_mjip_norm_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjip_norm_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:45.210823+00:00
-- url     : https://prove2.me/theorems/63e581d2-1188-52d7-9bf6-f6f3978f300f
-- title:
--   Orthonormal Chart Bounds: mjip norm le
-- statement:
--   The Orthonormal Chart Bounds construction uses the mjip norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L17-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjip_norm_le {n : ℕ} (p q : Fin n → ℂ) :
    ‖mjip p q‖ ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) := by sorry
