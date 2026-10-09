-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_poincare_eigenvalues_monodromy
-- name    : TeschlODE.PeriodicOrbits.poincare_eigenvalues_monodromy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T05:29:52.654825+00:00
-- url     : https://prove2.me/theorems/fa7570c8-ad4c-4052-92be-0a2daa881948
-- title:
--   Theorem 12.4 — eigenvalues of $dP_\Sigma(x_0)$ plus the value $1$ are the eigenvalues of the monodromy matrix $M_{x_0}(t_0)$
-- statement:
--   Throughout, $f \in C^k(M, \mathbb{R}^n)$ with $k \ge 1$ on an open set $M \subseteq \mathbb{R}^n$, $\Phi$ is its flow with maximal intervals $I_x$, and $x_0 \in M$ is a periodic point of period $T = T(x_0) > 0$ (standing assumptions of Chapter 6 and §12.1). Let $\Sigma = \{x \in U \mid S(x) = 0\}$ be a codimension-one submanifold through $x_0$ transversal to $f$ (6.23), and let $\tau$ be a $C^k$ return time to $\Sigma$ near $x_0$ with $\tau(x_0) = T$ (Lemma 6.9), so that $P_\Sigma(y) = \Phi(\tau(y), y)$ is the Poincaré map (12.9). Let
--   $$M_{x_0}(t_0) = \frac{\partial \Phi_T}{\partial x}\big(\Phi(t_0, x_0)\big)$$
--   be the **monodromy matrix** of the first variational equation along the orbit, based at $\Phi(t_0, x_0)$.
--
--   Then the derivative $dP_\Sigma(x_0)$ of the Poincaré map, an endomorphism of the $(n-1)$-dimensional tangent space $T_{x_0}\Sigma = \ker \frac{\partial S}{\partial x}(x_0)$, exists, and for every $t_0 \in \mathbb{R}$
--   $$\chi_{M_{x_0}(t_0)}(X) = (X - 1)\, \chi_{dP_\Sigma(x_0)}(X),$$
--   where $\chi$ denotes the characteristic polynomial. That is, the eigenvalues of $dP_\Sigma(x_0)$ plus the single value $1$ coincide, with algebraic multiplicities, with the eigenvalues of $M_{x_0}(t_0)$. In particular, the eigenvalues of $dP_\Sigma(x_0)$ are independent of the base point on the orbit and of the transversal section $\Sigma$.
--
--   The theorem connects the two linear objects attached to a periodic orbit: the Poincaré map, a discrete dynamical system on a section, and the Floquet theory of the first variational equation. It is what makes stability criteria stated for one computable from the other.
--
--   **Formalization Note.** Eigenvalues are compared as roots of characteristic polynomials over $\mathbb{R}$, so multiplicities are included (an equality of eigenvalue *sets* would be weaker). The book prints the monodromy matrix as $\frac{\partial \Phi_{T - t_0}}{\partial x}(\Phi(t_0, x_0))$ on p. 316; this is a typo, since $M_{x_0}(t_0) = \Pi_{x_0}(t_0 + T, t_0) = \frac{\partial\Phi_T}{\partial x}(\Phi(t_0, x_0))$ by (12.5), and only this form satisfies (12.8); $\Phi_T$ is used. Independence of $\Sigma$ is immediate because the left side does not involve $\Sigma$; independence of the base point is carried by the quantifier over $t_0$. The section $\Sigma$ is the book's general one, not a hyperplane orthogonal to $f(x_0)$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 317, Theorem 12.4

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
import Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
import Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Theorem 12.4, p. 317. Let `f ∈ Cᵏ(M, ℝⁿ)`, `k ≥ 1`, `M` open, with flow `Φ`; let
`x₀` be a periodic point of period `T = T(x₀) > 0`; let `Σ = {x ∈ U | S(x) = 0}` be a
codimension-one submanifold through `x₀` transversal to `f` (6.23), and `P_Σ(y) = Φ(τ(y), y)`
the Poincaré map (6.25), (12.9), with `τ` a `Cᵏ` return time, `τ(x₀) = T` (Lemma 6.9). Then the
derivative `dP_Σ(x₀)` on `T_{x₀}Σ = ker (∂S/∂x)(x₀)` exists as an endomorphism `L`, and for
every `t₀` the monodromy matrix `M_{x₀}(t₀) = ∂Φ_T/∂x (Φ(t₀, x₀))` satisfies
`charpoly M_{x₀}(t₀) = (X − 1) · charpoly dP_Σ(x₀)`: the eigenvalues of `dP_Σ(x₀)` plus the single
value `1` are those of `M_{x₀}(t₀)`, with algebraic multiplicities. Since the left side does not
involve `Σ`, and `t₀` is arbitrary, the eigenvalues are independent of the section and of the
base point on the orbit. -/
theorem poincare_eigenvalues_monodromy {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T)
    (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (hsec : IsTransversalSection f M k U S)
    (hx₀U : x₀ ∈ U) (hSx₀ : S x₀ = 0)
    (τ : (Fin n → ℝ) → ℝ) (hτ : IsReturnTime I Φ k U S x₀ T τ) :
    ∃ L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ)),
      IsPoincareDerivative Φ τ S x₀ L ∧
      ∀ t₀ : ℝ,
        LinearMap.charpoly (fderiv ℝ (Φ T) (Φ t₀ x₀) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
          (Polynomial.X - 1) * L.charpoly := by sorry

end TeschlODE.PeriodicOrbits
