-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sum_log_dOf
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.sum_log_dOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:59.283286+00:00
-- url     : https://prove2.me/theorems/a40364df-6c02-4ba2-843c-d85a1451555f
-- title:
--   Orthonormal Chart Bounds: sum log d Of
-- statement:
--   The Orthonormal Chart Bounds construction uses the sum log d Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LogDOfPosBound.lean#L57-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LogDOfPosBound.lean#L57-L78

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.sum_log_dOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) : ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ = 0 := by sorry
