-- Prove2me | Theorems.Thm_PConeEB_corollary_3_1
-- name    : PConeEB.corollary_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:18.6114+00:00
-- url     : https://prove2.me/theorems/ab09e03b-9c83-464f-914f-ae8b8eb612f6
-- title:
--   Corollary 3.1 — best Hölderian bounds
-- statement:
--   Suppose (Feas) is feasible and items (i), (ii), (iii) of Theorem 3.2 hold for some $\mathfrak g=|\cdot|^\alpha$ with $\alpha\in(0,1)$. Then:
--
--   (a) $K$ and $\mathcal L+a$ satisfy a uniform Hölderian error bound with exponent $\alpha$.
--
--   (b) If moreover $\|z\|=1$, $\mathcal L=\{z\}^\perp$ and $a=0$, then for any consistent error bound function $\Phi$ for $K,\mathcal L$ and any $\hat\eta>0$ there are $\hat\kappa>0$ and $s_0>0$ such that
--   $$
--   s^\alpha\le\hat\kappa\,\Phi(\hat\kappa s,\hat\eta)\qquad\forall s\in[0,s_0].
--   $$
--   In particular, $K$ and $\mathcal L$ do not satisfy a uniform Hölderian error bound with exponent $\hat\alpha$ where $\alpha<\hat\alpha\le1$.
--
--   This is the form of Theorem 3.2 that is applied to the $p$-cone.
--
--   Differences from the source:
--   - generalization: K = K¹ × K² in PPS (iii) → K = K₁ + K₂ with K₁ ⊆ E₁, K₂ ⊆ E₂ for complementary subspaces E₁, E₂, not necessarily orthogonal; reason: orthogonal subspaces are the Cartesian case, so the hypothesis is weaker and the result covers the source; a linear isomorphism preserves polyhedrality, ri and Lipschitzian error bounds up to constants
--   - reading: ∂K, "the boundary" of K, for K possibly lower dimensional → frontier K, the topological boundary in E, inside gammaZ; reason: frontier K contains every relative boundary point, so the infimum runs over at least the same v; the proof of Theorem 2.2 needs exactly this, since the projection of q ∉ span K onto K can lie in ri K. For full-dimensional K the two notions coincide
--   - encoding: γ_{z,η} ∈ (0, ∞], with inf ∅ = +∞ → gammaZ in ENNReal, 0 < gammaZ K z g η; κ_{z,η} the real number kappaZ, with γ⁻¹ read as 0 at γ = ⊤; reason: the paper's own convention γ_{z,0} = ∞; kappaZ is used only under 0 < gammaZ
--   - encoding: (G1): w : (0, 1] → {z}^⊥ ∩ span K \ F continuous, L_g = limsup < ∞ → SatisfiesG1 with a total w, the conditions on Set.Ioc 0 1, and an ENNReal limsup equal to ENNReal.ofReal Lg with 0 ≤ Lg; reason: Lean conventions; same instances, and an ENNReal limsup has no boundedness side condition
--   - encoding: a finite dimensional Euclidean space E → a type E with InnerProductSpace ℝ E, FiniteDimensional ℝ E and CompleteSpace E; reason: Mathlib conventions; CompleteSpace is required by ProperCone.innerDual and holds in every finite dimensional space
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Corollary 3.1, p.15

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_IsNontrivialFace
import Definitions.Def_PConeEB_affineSet
import Definitions.Def_PConeEB_hyperplane
import Definitions.Def_PConeEB_IsPPS
import Definitions.Def_PConeEB_IsUniformHolderianEB
import Definitions.Def_PConeEB_gammaZ
import Definitions.Def_PConeEB_SatisfiesSH
import Definitions.Def_PConeEB_SatisfiesG1
import Definitions.Def_PConeEB_IsConsistentEBF

open MoreauProx.Decomposition (IsClosedConvexCone)

namespace PConeEB

/-- Corollary 3.1 (best Hölderian bounds). Suppose (Feas) is feasible and items (i), (ii), (iii) of
Theorem 3.2 hold for `g = |·|^α` with `α ∈ (0, 1)`. Then (a) `K` and `L + a` satisfy a uniform
Hölderian error bound with exponent `α`. (b) If moreover `‖z‖ = 1`, `L = {z}^⊥`, `a = 0`, then for
every consistent error bound function `Φ` for `K, L` and every `η̂ > 0` there are `κ̂, s₀ > 0` with
`s^α ≤ κ̂ Φ(κ̂ s, η̂)` on `[0, s₀]`, and `K, L` satisfy no uniform Hölderian error bound with exponent
`α̂` where `α < α̂ ≤ 1`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Corollary 3.1, p.15.

**Formalization Note.** `[CompleteSpace E]` is needed by `ProperCone.innerDual` and is automatic in
finite dimension. -/
theorem corollary_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {K : Set E} (hK : IsClosedConvexCone K)
    (L : Submodule ℝ E) (a : E) (hfeas : (affineSet L a ∩ K).Nonempty)
    {z : E} (hz : z ∈ ProperCone.innerDual K) (hzL : z ∈ Lᗮ) (hza : inner ℝ z a = 0)
    (hF : IsNontrivialFace K (K ∩ hyperplane z)) (hPPS : IsPPS (K ∩ hyperplane z) L a)
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (hγ : ∀ η, 0 < η → 0 < gammaZ K z (fun t => |t| ^ α) η)
    (hSH : SatisfiesSH fun t => |t| ^ α)
    (hG1 : ∃ (v : E) (w : ℝ → E) (Lg : ℝ), SatisfiesG1 K z (fun t => |t| ^ α) v w Lg) :
    IsUniformHolderianEB K (affineSet L a) α ∧
    (‖z‖ = 1 → (L : Set E) = hyperplane z → a = 0 →
      (∀ Φ : ℝ → ℝ → ℝ, IsConsistentEBF ![K, hyperplane z] Φ →
        ∀ ηhat : ℝ, 0 < ηhat →
          ∃ κhat : ℝ, 0 < κhat ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ Set.Icc 0 s₀,
            s ^ α ≤ κhat * Φ (κhat * s) ηhat) ∧
      ∀ αhat : ℝ, α < αhat → αhat ≤ 1 → ¬ IsUniformHolderianEB K (hyperplane z) αhat) := by sorry

end PConeEB
