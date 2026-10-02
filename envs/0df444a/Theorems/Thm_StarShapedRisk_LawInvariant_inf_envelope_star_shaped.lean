-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_inf_envelope_star_shaped
-- name    : StarShapedRisk.LawInvariant.inf_envelope_star_shaped
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T13:37:25.533613+00:00
-- url     : https://prove2.me/theorems/0b13a551-04b0-4a81-a806-1afd0bd7c783
-- title:
--   Inf-envelope over a shrinking-stable family of jointly-homogeneous functionals is superhomogeneous
-- statement:
--   The engine of the star-shapedness step in Castagnoli et al. (2022), Theorem 5, (ii)=>(i): if each component functional satisfies phi_g(tX) = t * phi_{t^{-1}g}(X) for t > 1 and the benchmark family G is stable under shrinking (t^{-1} g in G), then the envelope rho(X) = inf_{g in G} phi_g(X) is positively superhomogeneous: t * rho(X) <= rho(tX) for t > 1. With phi_g(X) = sup_alpha (VaR_alpha(X) - g(alpha)) this is the paper's computation rho(lambda X) >= lambda rho(X).

import Mathlib

namespace StarShapedRisk.LawInvariant

/-- Castagnoli et al. (2022), proof of Theorem 5, `(ii) ⇒ (i)` star-shapedness
    (p. 2647): if each component `φ g` satisfies the joint homogeneity
    `φ g (t • X) = (t : EReal) * φ ((t⁻¹ : ℝ) • g) X` for `t > 1` and the index family `G`
    is stable under shrinking (`t⁻¹ • g ∈ G` for `t > 1`), then the envelope
    `ρ X = ⨅ g ∈ G, φ g X` is positively superhomogeneous:
    `(t : EReal) * ρ X ≤ ρ (t • X)` for `t > 1`. Proof:
    `ρ (t • X) = ⨅ g ∈ G, (t : EReal) * φ ((t⁻¹ : ℝ) • g) X`
    `= (t : EReal) * ⨅ h ∈ (t⁻¹ : ℝ) • G, φ h X`
    `≥ (t : EReal) * ⨅ g ∈ G, φ g X = (t : EReal) * ρ X`,
    using `t⁻¹ • G ⊆ G`. With `φ g X = ⨆ α, (VaR_α X - g α)` this is exactly
    the paper's computation `ρ(λX) ≥ λρ(X)`. -/
theorem inf_envelope_star_shaped {E : Type*} [AddCommGroup E] [Module ℝ E]
    (φ : (Set.Ioo (0 : ℝ) 1 → ℝ) → E → EReal)
    (G : Set (Set.Ioo (0 : ℝ) 1 → ℝ))
    (hφ : ∀ g ∈ G, ∀ {t : ℝ}, 1 < t → ∀ X : E,
      φ g (t • X) = ((t : EReal) * φ ((t⁻¹ : ℝ) • g) X))
    (hG : ∀ {t : ℝ}, 1 < t → ∀ g ∈ G, (t⁻¹ : ℝ) • g ∈ G)
    {t : ℝ} (ht : 1 < t) (X : E) :
    (t : EReal) * (⨅ g ∈ G, φ g X) ≤ ⨅ g ∈ G, φ g (t • X) := by
  sorry

end StarShapedRisk.LawInvariant
