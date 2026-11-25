-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_ubasis_at
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.ubasis_at
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:18.603019+00:00
-- url     : https://prove2.me/theorems/25086a90-c5e7-503e-b2fd-d393b4714d1f
-- title:
--   Orthonormal Perp Basis: ubasis at
-- statement:
--   The Orthonormal Perp Basis construction uses the ubasis at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UbasisAt.lean#L228-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UbasisAt.lean#L228-L387

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UbasisAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.ubasis_at (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r) (hξ0 : ξ ≠ 0) (hiso : herm X.Gm ξ ξ = 0)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (ho : X.IsOrtho x0) (hflag : X.SameFlag z0 x0) (τ : X.Ψ) :
    ∃ fτ : Fin (r - 2) → Fin r → ℂ,
      (∀ k, hermC τ.1 X.Gm (fτ k) (Data.emb τ.1 ξ) = 0 ∧
        hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ (fτ k) - fτ k)) (Data.emb τ.1 ξ) = 0) ∧
      (∀ k, I • ((2 : ℂ) • X.ppos z0 τ (fτ k) - fτ k) = (if (k : ℕ) < X.p0 - 1 then I else -I) • fτ k) ∧
      (∀ k l, hermC τ.1 X.Gm (fτ k) (fτ l) =
        if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0) ∧
      (∀ c : Fin (r - 2) → ℂ, X.maj z0 τ (∑ k, c k • fτ k) = ∑ k, ‖c k‖ ^ 2) ∧
      (∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
        hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ v - v)) (Data.emb τ.1 ξ) = 0 →
        v ∈ Submodule.span ℂ (Set.range fτ)) := by sorry
