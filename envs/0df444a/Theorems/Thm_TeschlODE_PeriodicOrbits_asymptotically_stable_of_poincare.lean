-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_asymptotically_stable_of_poincare
-- name    : TeschlODE.PeriodicOrbits.asymptotically_stable_of_poincare
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:02:52.947151+00:00
-- url     : https://prove2.me/theorems/f55b0799-cdc6-4b4b-8b4e-79966b7ee72b
-- title:
--   Corollary 12.3 — eigenvalues of $dP_\Sigma(x_0)$ inside the unit circle imply asymptotic stability of the orbit
-- statement:
--   Throughout, $f \in C^k(M, \mathbb{R}^n)$ with $k \ge 1$ on an open set $M \subseteq \mathbb{R}^n$, $\Phi$ is its flow with maximal intervals $I_x$, and $x_0 \in M$ is a periodic point of period $T = T(x_0) > 0$ (standing assumptions of Chapter 6 and §12.1). Let $\Sigma = \{x \in U \mid S(x) = 0\}$ be a codimension-one submanifold through $x_0$ transversal to $f$ (6.23), and let $\tau$ be a $C^k$ return time to $\Sigma$ near $x_0$ with $\tau(x_0) = T$ (Lemma 6.9), so that $P_\Sigma(y) = \Phi(\tau(y), y)$ is the Poincaré map (12.9).
--
--   If all eigenvalues of the derivative $dP_\Sigma(x_0)$ of the Poincaré map lie inside the unit circle,
--   $$\sigma\big(dP_\Sigma(x_0)\big) \subseteq \{z \in \mathbb{C} : |z| < 1\},$$
--   then the periodic orbit $\gamma(x_0)$ is asymptotically stable in the sense of (12.1).
--
--   This is the linearized stability test for periodic orbits; together with Theorem 12.4 it becomes a condition on the Floquet multipliers of the first variational equation other than the trivial multiplier $1$.
--
--   **Formalization Note.** $dP_\Sigma(x_0)$ is an endomorphism $L$ of $\ker \frac{\partial S}{\partial x}(x_0)$ characterized by `IsPoincareDerivative`; the hypothesis asserts that such an $L$ exists and that every complex root $z$ of its characteristic polynomial has $|z| < 1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 317, Corollary 12.3

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
import Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
import Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative
import Definitions.Def_TeschlODE_PeriodicOrbits_orbit
import Definitions.Def_TeschlODE_PeriodicOrbits_IsAsymptoticallyStableOrbit

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Corollary 12.3, p. 317. Let `f ∈ Cᵏ(M, ℝⁿ)`, `k ≥ 1`, have a periodic orbit `γ(x₀)`
(`x₀` periodic of period `T > 0`), let `Σ = {x ∈ U | S(x) = 0}` be a transversal section through
`x₀` with Poincaré map `P_Σ(y) = Φ(τ(y), y)`. If all eigenvalues of `dP_Σ(x₀)` (the complex roots
of the characteristic polynomial of `L`, the derivative on `ker (∂S/∂x)(x₀)`) lie inside the unit
circle, then `γ(x₀)` is an asymptotically stable orbit (12.1). -/
theorem asymptotically_stable_of_poincare {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T)
    (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (hsec : IsTransversalSection f M k U S)
    (hx₀U : x₀ ∈ U) (hSx₀ : S x₀ = 0)
    (τ : (Fin n → ℝ) → ℝ) (hτ : IsReturnTime I Φ k U S x₀ T τ)
    (hL : ∃ L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ)),
      IsPoincareDerivative Φ τ S x₀ L ∧
      ∀ z : ℂ, (L.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ < 1) :
    IsAsymptoticallyStableOrbit M I Φ (orbit I Φ x₀) := by sorry

end TeschlODE.PeriodicOrbits
