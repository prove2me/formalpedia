-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_planar_divergence_stability
-- name    : TeschlODE.PeriodicOrbits.planar_divergence_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:19:10.425813+00:00
-- url     : https://prove2.me/theorems/31df6106-4a73-49c1-bf28-76a1c1015b2f
-- title:
--   Lemma 12.6 — planar periodic orbit: $\int_0^T \operatorname{div} f < 0$ gives asymptotic stability, $> 0$ instability
-- statement:
--   Let $f \in C^k(M, \mathbb{R}^2)$, $k \ge 1$, be a planar vector field on an open set $M \subseteq \mathbb{R}^2$ with flow $\Phi$ (maximal intervals $I_x$), and let $x_0 \in M$ be a periodic point of period $T > 0$. Write $\operatorname{div} f(x) = \operatorname{tr} df_x$. Then the periodic orbit $\gamma(x_0)$ is asymptotically stable if
--   $$\int_0^T \operatorname{div} f(\Phi(t, x_0))\, dt < 0 \qquad (12.12)$$
--   and unstable (not stable) if the integral is positive.
--
--   In the plane the Poincaré map is one-dimensional, so its single eigenvalue equals the determinant of the monodromy matrix, which Liouville's formula expresses through the divergence; the lemma turns this into a directly computable test.
--
--   **Formalization Note.** The book says "a periodic point $x_0$ is asymptotically stable"; in this chapter that refers to the orbit $\gamma(x_0)$ (definition (12.1)), which is what is stated. The integrand is continuous along the orbit, so the interval integral is a genuine Riemann integral.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 319, Lemma 12.6, Eq. (12.12)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_orbit
import Definitions.Def_TeschlODE_PeriodicOrbits_IsStableOrbit
import Definitions.Def_TeschlODE_PeriodicOrbits_IsAsymptoticallyStableOrbit

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Lemma 12.6, p. 319. Let `f ∈ Cᵏ(M, ℝ²)`, `k ≥ 1`, be a planar vector field with flow
`Φ`, and `x₀` a periodic point of period `T > 0`. If `∫₀ᵀ div f(Φ(t, x₀)) dt < 0` (12.12) then the
periodic orbit `γ(x₀)` is asymptotically stable; if the integral is positive it is unstable (not
stable). Here `div f(x) = tr df_x`. -/
theorem planar_divergence_stability (f : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (M : Set (Fin 2 → ℝ))
    (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin 2 → ℝ) → Set ℝ) (Φ : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin 2 → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T) :
    ((∫ t in (0 : ℝ)..T,
        LinearMap.trace ℝ (Fin 2 → ℝ)
          (fderiv ℝ f (Φ t x₀) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) < 0 →
      IsAsymptoticallyStableOrbit M I Φ (orbit I Φ x₀)) ∧
    (0 < (∫ t in (0 : ℝ)..T,
        LinearMap.trace ℝ (Fin 2 → ℝ)
          (fderiv ℝ f (Φ t x₀) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) →
      ¬ IsStableOrbit M I Φ (orbit I Φ x₀)) := by sorry

end TeschlODE.PeriodicOrbits
