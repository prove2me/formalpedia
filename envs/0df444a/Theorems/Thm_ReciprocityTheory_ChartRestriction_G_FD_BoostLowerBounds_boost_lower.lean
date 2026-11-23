-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_boost_lower
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.boost_lower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:18.272807+00:00
-- url     : https://prove2.me/theorems/7f2d9a95-2f4d-4e5c-b792-054bb70bd7f0
-- title:
--   Boost Lower Bounds: boost lower
-- statement:
--   The Boost Lower Bounds construction uses the boost lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L224-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L224-L281

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz

theorem ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.boost_lower (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (w : Fin r → ℂ) :
    min (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w ≤
      X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) := by sorry
