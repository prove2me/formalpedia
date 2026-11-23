-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_Bf_gv_zero
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_gv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:24.947821+00:00
-- url     : https://prove2.me/theorems/cb080008-47f9-4fb6-add1-ed3e83a6d69a
-- title:
--   Orthonormal Chart Bounds: Bf gv zero
-- statement:
--   The Orthonormal Chart Bounds construction uses the Bf gv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L137-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BfSubRight.lean#L137-L174

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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_gv_zero (Z : X.Coord) (τ : X.Ψ) (hdet : ∀ c : Fin r, (blk (Gp X Z τ) c).det ≠ 0) (k : Fin r)
    (t : Fin r → ℂ) (ht : ∀ b, k ≤ b → t b = 0) :
    Bf X Z τ (fun a => uMat (Gp X Z τ) a k) t = 0 := by sorry
