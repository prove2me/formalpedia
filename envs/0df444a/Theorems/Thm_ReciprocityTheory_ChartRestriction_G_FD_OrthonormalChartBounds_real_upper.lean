-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_real_upper
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.real_upper
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:08.783613+00:00
-- url     : https://prove2.me/theorems/4a312fc7-c55d-5ca2-84cd-428631a7affd
-- title:
--   Orthonormal Chart Bounds: real upper
-- statement:
--   The Orthonormal Chart Bounds construction uses the real upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealLower2.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealLower2.lean#L10-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealLower2
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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.real_upper {ρ α β Q : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 ≤ ρ)
    (hQ : Q * (1 - ρ ^ 2) ≤ (α + ρ * β) ^ 2) :
    2 * Q - (α ^ 2 - β ^ 2) ≤ (1 + ρ) / (1 - ρ) * (α ^ 2 + β ^ 2) := by sorry
