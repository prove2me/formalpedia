-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_det_poincare_eq_det_monodromy
-- name    : TeschlODE.PeriodicOrbits.det_poincare_eq_det_monodromy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:08:37.637876+00:00
-- url     : https://prove2.me/theorems/f657fdce-0d25-4ad7-97b8-da7ba52b018e
-- title:
--   Corollary 12.5 — $\det dP_\Sigma(x_0) = \det M_{x_0}(t_0) \neq 0$, and $P_\Sigma$ is a local diffeomorphism at $x_0$
-- statement:
--   Throughout, $f \in C^k(M, \mathbb{R}^n)$ with $k \ge 1$ on an open set $M \subseteq \mathbb{R}^n$, $\Phi$ is its flow with maximal intervals $I_x$, and $x_0 \in M$ is a periodic point of period $T = T(x_0) > 0$ (standing assumptions of Chapter 6 and §12.1). Let $\Sigma = \{x \in U \mid S(x) = 0\}$ be a codimension-one submanifold through $x_0$ transversal to $f$ (6.23), and let $\tau$ be a $C^k$ return time to $\Sigma$ near $x_0$ with $\tau(x_0) = T$ (Lemma 6.9), so that $P_\Sigma(y) = \Phi(\tau(y), y)$ is the Poincaré map (12.9). Let $M_{x_0}(t_0) = \frac{\partial \Phi_T}{\partial x}(\Phi(t_0, x_0))$ be the monodromy matrix.
--
--   Then the derivative $dP_\Sigma(x_0)$ (an endomorphism of $T_{x_0}\Sigma = \ker\frac{\partial S}{\partial x}(x_0)$) exists and for every $t_0 \in \mathbb{R}$
--   $$\det\big(dP_\Sigma(x_0)\big) = \det\big(M_{x_0}(t_0)\big) \neq 0. \qquad (12.10)$$
--   Moreover $P_\Sigma$ is a local diffeomorphism of $\Sigma$ at $x_0$: there are open sets $W, W' \ni x_0$ such that $P_\Sigma$ is defined and $C^k$ on $W$ and maps $W \cap \Sigma$ bijectively onto $W' \cap \Sigma$, with inverse the restriction of a map $Q$ that is $C^k$ on $W'$.
--
--   By Liouville's formula the common value equals $\exp \int_0^T \operatorname{div} f(\Phi(t, x_0))\,dt$ (12.11), which is the route to Lemma 12.6.
--
--   **Formalization Note.** "Local diffeomorphism at $x_0$" for a map of the embedded submanifold $\Sigma$ is stated concretely: bijection between relatively open pieces $W \cap \Sigma$ and $W' \cap \Sigma$ of $\Sigma$, $C^k$ in the sense of $C^k$ maps on open subsets of $\mathbb{R}^n$ restricted to $\Sigma$. The clause "since the determinant of the monodromy matrix does not vanish" is included as the conjunct $\det M_{x_0}(t_0) \neq 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 318, Corollary 12.5, Eq. (12.10)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
import Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
import Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Corollary 12.5, p. 318. In the setting of Theorem 12.4 (periodic point `x₀` of period
`T > 0`, transversal section `Σ = {x ∈ U | S(x) = 0}` through `x₀`, Poincaré map
`P_Σ(y) = Φ(τ(y), y)`): the derivative `dP_Σ(x₀)` (endomorphism `L` of `ker (∂S/∂x)(x₀)`) exists
and (12.10) `det dP_Σ(x₀) = det M_{x₀}(t₀)` for every `t₀`, where `M_{x₀}(t₀) = ∂Φ_T/∂x (Φ(t₀, x₀))`;
this determinant does not vanish; and `P_Σ` is a local diffeomorphism of `Σ` at `x₀`: there are
open `W, W' ∋ x₀` such that `P_Σ` is defined and `Cᵏ` on `W`, maps `W ∩ Σ` bijectively onto
`W' ∩ Σ`, and has there an inverse which is the restriction of a map `Q` that is `Cᵏ` on `W'`. -/
theorem det_poincare_eq_det_monodromy {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T)
    (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (hsec : IsTransversalSection f M k U S)
    (hx₀U : x₀ ∈ U) (hSx₀ : S x₀ = 0)
    (τ : (Fin n → ℝ) → ℝ) (hτ : IsReturnTime I Φ k U S x₀ T τ) :
    (∃ L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ)),
      IsPoincareDerivative Φ τ S x₀ L ∧
      ∀ t₀ : ℝ,
        LinearMap.det L =
          LinearMap.det (fderiv ℝ (Φ T) (Φ t₀ x₀) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∧
        LinearMap.det (fderiv ℝ (Φ T) (Φ t₀ x₀) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0) ∧
    ∃ W W' : Set (Fin n → ℝ), IsOpen W ∧ IsOpen W' ∧ x₀ ∈ W ∧ x₀ ∈ W' ∧
      (∀ y ∈ W, y ∈ M ∧ τ y ∈ I y) ∧
      ContDiffOn ℝ k (fun y => Φ (τ y) y) W ∧
      Set.BijOn (fun y => Φ (τ y) y) {y | y ∈ W ∧ y ∈ U ∧ S y = 0} {y | y ∈ W' ∧ y ∈ U ∧ S y = 0} ∧
      ∃ Q : (Fin n → ℝ) → (Fin n → ℝ), ContDiffOn ℝ k Q W' ∧
        Set.LeftInvOn Q (fun y => Φ (τ y) y) {y | y ∈ W ∧ y ∈ U ∧ S y = 0} := by sorry

end TeschlODE.PeriodicOrbits
