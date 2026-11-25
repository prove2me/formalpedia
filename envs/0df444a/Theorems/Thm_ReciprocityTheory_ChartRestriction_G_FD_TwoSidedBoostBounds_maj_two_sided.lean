-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_maj_two_sided
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.maj_two_sided
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:45.546523+00:00
-- url     : https://prove2.me/theorems/a69327b2-cf8a-549e-83ba-8457037eff3f
-- title:
--   Two Sided Boost Bounds: maj two sided
-- statement:
--   The Two Sided Boost Bounds construction uses the maj two sided property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TwoSidedBoostBounds.lean#L43-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TwoSidedBoostBounds.lean#L43-L114

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.maj_two_sided {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hy : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) ∧
    min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w ≤
      X.maj (X.flow ξ s x) τ w ∧
    X.maj (X.flow ξ s x) τ w ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w := by sorry
