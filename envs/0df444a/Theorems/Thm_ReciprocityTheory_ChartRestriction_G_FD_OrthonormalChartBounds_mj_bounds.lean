-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_mj_bounds
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mj_bounds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:25.775983+00:00
-- url     : https://prove2.me/theorems/a337fe91-110c-4e16-a1fc-b4b7e8cf13af
-- title:
--   Orthonormal Chart Bounds: mj bounds
-- statement:
--   The Orthonormal Chart Bounds construction uses the mj bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealLower2.lean#L59-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealLower2.lean#L59-L187

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
set_option maxHeartbeats 800000

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mj_bounds {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 10) {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (hy : X.xZ x Z ∈ X.dom) (τ : X.Ψ)
    (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by sorry
