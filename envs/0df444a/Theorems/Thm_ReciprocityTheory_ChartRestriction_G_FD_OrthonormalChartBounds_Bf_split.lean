-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Bf_split
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:52.326387+00:00
-- url     : https://prove2.me/theorems/4a86f68a-9aad-4e8d-889b-873054930138
-- title:
--   Orthonormal Chart Bounds: Bf split
-- statement:
--   The Orthonormal Chart Bounds construction uses the Bf split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PivotNeg.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PivotNeg.lean#L17-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PivotNeg
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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_split (Z : X.Coord) (τ : X.Ψ) (v t : Fin r → ℂ) (h1 : Bf X Z τ v t = 0) :
    Bf X Z τ v v = Bf X Z τ (v - t) (v - t) - Bf X Z τ t t := by sorry
