-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Bf_self_re
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_self_re
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:32.612606+00:00
-- url     : https://prove2.me/theorems/d6df0bb3-bcee-478c-ab90-ca899faffc9c
-- title:
--   Orthonormal Chart Bounds: Bf self re
-- statement:
--   The Orthonormal Chart Bounds construction uses the Bf self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L176-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L176-L181

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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_self_re (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) :
    (Bf X Z τ v v).re = nsq (Pv X v) - nsq (Nv X Z τ v) := by sorry
