-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_det_lowBlock
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.det_lowBlock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:26.954473+00:00
-- url     : https://prove2.me/theorems/7a140392-8e9a-4e56-8e81-f4a1da38cb6f
-- title:
--   Orthonormal Chart Bounds: det low Block
-- statement:
--   The Orthonormal Chart Bounds construction uses the det low Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SignTypeCancelIdentity.lean#L66-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SignTypeCancelIdentity.lean#L66-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
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
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by sorry
