-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_hartman_grobman
-- name    : TeschlODE.LocalBehavior.hartman_grobman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:51:55.384621+00:00
-- url     : https://prove2.me/theorems/7522aca5-d64a-41a5-8e81-5158814d6528
-- title:
--   Theorem 9.9 (Hartman–Grobman) — a C¹ flow is locally conjugate to e^{tA} near a hyperbolic fixed point
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open with $0 \in M$, and let $f : M \to \mathbb{R}^n$ be a $C^1$ vector field with $f(0) = 0$. Let $A = df_0$ be the Jacobian matrix of $f$ at $0$ and suppose $0$ is a **hyperbolic** fixed point: no eigenvalue of $A$ has zero real part. Let $\Phi(t, x)$, $t \in I_x$, be the (local) flow of $\dot x = f(x)$. Then there is a homeomorphism $\phi(x) = x + h(x)$ of $\mathbb{R}^n$ with $h$ bounded such that
--   $$\phi \circ e^{tA} = \Phi_t \circ \phi \qquad (9.34)$$
--   in a sufficiently small neighborhood of $0$: there is a neighborhood $U$ of $0$ such that for all $x \in \mathbb{R}^n$ and $t \in \mathbb{R}$ with $e^{sA}x \in U$ for every $s$ between $0$ and $t$,
--   $$t \in I_{\phi(x)} \quad\text{and}\quad \phi(e^{tA} x) = \Phi(t, \phi(x)).$$
--
--   Near a hyperbolic equilibrium the orbits of the nonlinear flow are therefore continuous deformations of those of its linearization, and the local phase portrait is determined by $A$.
--
--   **Formalization Note.** The book says "differentiable vector field"; the proof (pp. 264–266) uses continuity of $\partial f/\partial x$ (Gronwall on the variational equation (9.35) and the cut-off estimate), so $f$ is taken $C^1$ on the open phase space $M$ of Chapter 6 (`ContDiffOn ℝ 1 f M`). The flow is local, characterized by `IsMaximalFlow`. "In a sufficiently small neighborhood of $0$" is read as $\exists U \in \mathcal{N}(0)$, with $\phi$ chosen first, and the identity is asserted along every linear orbit segment $\{e^{sA}x : s \text{ between } 0 \text{ and } t\}$ that stays in $U$ (both signs of $t$); the conclusion includes that $\Phi(t, \phi(x))$ is defined. This is the domain on which the book's proof gives the identity: its global conjugacy for the cut-off field $\tilde f$ agrees with $\Phi$ as long as the orbit stays where $\tilde f = f$. The conjugacy at the fixed point $0$ alone is trivial and is not what is stated. $|\cdot|$ is the sup norm on `Fin n → ℝ`; boundedness of $h$ and neighborhoods do not depend on the norm. $e^{tA}$ is `NormedSpace.exp (t • A)`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 264, Theorem 9.9

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.LocalBehavior

/-- Teschl, Theorem 9.9 (Hartman–Grobman), p. 264. `f` is a C¹ vector field on the open set
`M ⊆ ℝⁿ` (the book's "differentiable"; its proof uses continuity of `∂f/∂x`) with the hyperbolic
fixed point `0`: `f 0 = 0` and no eigenvalue of the Jacobian matrix `A = df₀` has zero real part.
`Φ` is the (local) flow of `ẋ = f(x)` with maximal intervals `I x`. Then there is a homeomorphism
`ϕ = id + h` of `ℝⁿ` with `h` bounded such that `ϕ ∘ e^{tA} = Φ_t ∘ ϕ` (9.34) in a sufficiently
small neighborhood of `0`, read as: there is a neighborhood `U` of `0` such that for all `x`, `t`
with `e^{sA} x ∈ U` for every `s` between `0` and `t`, the time `t` lies in the maximal interval
of `ϕ x` and `ϕ (e^{tA} x) = Φ(t, ϕ x)`. -/
theorem hartman_grobman {n : ℕ} (M : Set (Fin n → ℝ)) (hM : IsOpen M)
    (h0M : (0 : Fin n → ℝ) ∈ M) (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiffOn ℝ 1 f M)
    (hf0 : f 0 = 0) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A = LinearMap.toMatrix' (fderiv ℝ f 0 : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hhyp : ∀ z ∈ eigenvalues A, z.re ≠ 0)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ) :
    ∃ ϕ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), (∃ C : ℝ, ∀ x, ‖ϕ x - x‖ ≤ C) ∧
      ∃ U ∈ nhds (0 : Fin n → ℝ), ∀ (x : Fin n → ℝ) (t : ℝ),
        (∀ s ∈ Set.uIcc 0 t, (NormedSpace.exp (s • A)).mulVec x ∈ U) →
          t ∈ I (ϕ x) ∧ ϕ ((NormedSpace.exp (t • A)).mulVec x) = Φ t (ϕ x) := by sorry

end TeschlODE.LocalBehavior
