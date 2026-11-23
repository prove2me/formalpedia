-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Bf_coord
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_coord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:30.8474+00:00
-- url     : https://prove2.me/theorems/7d9dfd22-a8ec-401d-97ef-0b735d401c96
-- title:
--   Orthonormal Chart Bounds: Bf coord
-- statement:
--   The Orthonormal Chart Bounds construction uses the Bf coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L67-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L67-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_coord (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) :
    Bf X Z τ v w = ∑ a, Pv X v a * conj (Pv X w a) - ∑ m, Nv X Z τ v m * conj (Nv X Z τ w m) := by sorry
