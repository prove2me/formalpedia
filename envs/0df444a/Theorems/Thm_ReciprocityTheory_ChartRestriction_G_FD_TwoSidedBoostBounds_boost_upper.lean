-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_boost_upper
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.boost_upper
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:44.582992+00:00
-- url     : https://prove2.me/theorems/c9268542-e598-50c9-840f-cd1fb3509157
-- title:
--   Two Sided Boost Bounds: boost upper
-- statement:
--   The Two Sided Boost Bounds construction uses the boost upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TwoSidedBoostBounds.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TwoSidedBoostBounds.lean#L14-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.boost_upper (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
    (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) ≤
      max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := by sorry
