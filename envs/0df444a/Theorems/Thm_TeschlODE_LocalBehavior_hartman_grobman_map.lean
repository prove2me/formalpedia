-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_hartman_grobman_map
-- name    : TeschlODE.LocalBehavior.hartman_grobman_map
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:43:11.649806+00:00
-- url     : https://prove2.me/theorems/a322d86b-9b33-4f23-acab-1218b8267f95
-- title:
--   Theorem 10.4 (Hartman–Grobman for maps) — local conjugacy ϕ ∘ A = f ∘ ϕ near a hyperbolic fixed point
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}^n$ be a local diffeomorphism with fixed point $f(0) = 0$, and let $A = df_0$ be its Jacobian matrix at $0$. Suppose $0$ is hyperbolic, i.e. no eigenvalue of $A$ lies on the unit circle. Then there is a homeomorphism $\phi(x) = x + h(x)$ of $\mathbb{R}^n$ with $h$ bounded such that
--   $$\phi \circ A = f \circ \phi \qquad (10.31)$$
--   in a sufficiently small neighborhood of $0$.
--
--   Near a hyperbolic fixed point, a map is therefore topologically indistinguishable from its linearization; in particular its stable and unstable sets are locally homeomorphic images of $E^\pm(A)$.
--
--   **Formalization Note.** "Local diffeomorphism" is read as: $f$ is $C^1$ on $\mathbb{R}^n$ and $df_x$ is invertible at every $x$ (by the inverse function theorem this is exactly a $C^1$ local diffeomorphism). "In a sufficiently small neighborhood of $0$" is read as $\exists V \in \mathcal{N}(0),\ \forall x \in V,\ \phi(Ax) = f(\phi(x))$, with $\phi$ chosen before $V$. The conjugacy at the single point $0$ alone would be trivial (both sides are $0$), and is not what is stated. Boundedness of $h$ is $\exists C, \forall x, |\phi(x) - x| \le C$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 286, Theorem 10.4

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues

namespace TeschlODE.LocalBehavior

/-- Teschl, Theorem 10.4 (Hartman–Grobman for maps), p. 286. `f : ℝⁿ → ℝⁿ` is a (C¹) local
diffeomorphism — continuously differentiable with invertible derivative at every point — with
fixed point `0`, and `A = df₀` (the Jacobian matrix of `f` at `0`) has no eigenvalue on the unit
circle (0 is hyperbolic). Then there is a homeomorphism `ϕ = id + h` with `h` bounded such that
`ϕ ∘ A = f ∘ ϕ` (10.31) in a sufficiently small neighborhood of `0`, read as: on some
neighborhood `V` of `0`. -/
theorem hartman_grobman_map {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 1 f)
    (hloc : ∀ x, Function.Bijective (fderiv ℝ f x)) (hf0 : f 0 = 0)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A = LinearMap.toMatrix' (fderiv ℝ f 0 : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hhyp : ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) :
    ∃ ϕ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), (∃ C : ℝ, ∀ x, ‖ϕ x - x‖ ≤ C) ∧
      ∃ V ∈ nhds (0 : Fin n → ℝ), ∀ x ∈ V, ϕ (A.mulVec x) = f (ϕ x) := by sorry

end TeschlODE.LocalBehavior
