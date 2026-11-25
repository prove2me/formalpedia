-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_mjip_single
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjip_single
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:29.402866+00:00
-- url     : https://prove2.me/theorems/1304c48e-97b8-59f1-bab7-92bf460403f2
-- title:
--   Orthonormal Chart Bounds: mjip single
-- statement:
--   The Orthonormal Chart Bounds construction uses the mjip single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L24-L27

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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjip_single {n : ℕ} (p : Fin n → ℂ) (d : Fin n) : mjip p (Pi.single d 1) = p d := by sorry
