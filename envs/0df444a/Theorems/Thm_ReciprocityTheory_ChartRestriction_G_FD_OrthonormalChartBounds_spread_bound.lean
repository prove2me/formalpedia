-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_spread_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.spread_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:18.056845+00:00
-- url     : https://prove2.me/theorems/83433603-4859-4115-b9e6-da3318b41795
-- title:
--   Orthonormal Chart Bounds: spread bound
-- statement:
--   The Orthonormal Chart Bounds construction uses the spread bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LogDOfPosBound.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LogDOfPosBound.lean#L10-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PivotNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.spread_bound {n : ℕ} (f Δ : Fin n → ℝ) (h0 : ∑ k, Δ k = 0) :
    |∑ k, f k * Δ k| ≤ ((⨆ k, f k) - ⨅ k, f k) * ∑ k, |Δ k| := by sorry
