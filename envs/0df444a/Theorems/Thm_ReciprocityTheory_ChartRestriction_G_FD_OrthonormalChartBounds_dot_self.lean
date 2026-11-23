-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_dot_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.dot_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:31.51293+00:00
-- url     : https://prove2.me/theorems/10092024-56bf-4d36-923e-4bb65f916cf5
-- title:
--   Orthonormal Chart Bounds: dot self
-- statement:
--   The Orthonormal Chart Bounds construction uses the dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PosDefOfBound.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PosDefOfBound.lean#L10-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
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
open scoped ComplexConjugate ComplexOrder
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by sorry
