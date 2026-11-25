-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_mj_coord
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mj_coord
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:39.52268+00:00
-- url     : https://prove2.me/theorems/596f1c45-3505-5c94-850b-0544a0a04620
-- title:
--   Orthonormal Chart Bounds: mj coord
-- statement:
--   The Orthonormal Chart Bounds construction uses the mj coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L144-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L144-L200

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mj_coord {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (hy : X.xZ x Z ∈ X.dom)
    (τ : X.Ψ) (w : Fin r → ℂ) : ∃ γ : Fin X.p0 → ℂ,
      X.maj (X.xZ x Z) τ (mat x τ *ᵥ w) =
        2 * (nsq γ - nsq (Matrix.of (Z τ) *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) ∧
      ∀ δ, mjip (mjpa X w) δ - mjip (mjpb X w) (Matrix.of (Z τ) *ᵥ δ) =
        mjip γ δ - mjip (Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by sorry
