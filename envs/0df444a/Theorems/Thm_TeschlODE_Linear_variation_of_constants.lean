-- Prove2me | Theorems.Thm_TeschlODE_Linear_variation_of_constants
-- name    : TeschlODE.Linear.variation_of_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:57:30.147337+00:00
-- url     : https://prove2.me/theorems/4d98bf04-d32d-4b0b-a64a-09cd1823c568
-- title:
--   Theorem 3.12 — variation of constants formula (3.97)
-- statement:
--   Let $I$ be an interval, $A \in C(I, \mathbb{R}^{n\times n})$, $g \in C(I, \mathbb{R}^n)$, $t_0 \in I$, $x_0 \in \mathbb{R}^n$, and let $\Phi$ be the principal matrix solution of $\dot x = A(t)x$ on $I$. Then the solution of the inhomogeneous system
--   $$\dot x = A(t)x + g(t), \qquad x(t_0) = x_0 \qquad (3.92)$$
--   is
--   $$x(t) = \Phi(t,t_0)\,x_0 + \int_{t_0}^{t} \Phi(t,s)\,g(s)\,ds, \qquad t \in I. \qquad (3.97)$$
--
--   The formula reduces every inhomogeneous linear problem to the homogeneous one and underlies the perturbation results of Section 3.7.
--
--   **Formalization Note.** "The solution … is given by" is stated in both directions: the right-hand side of (3.97) solves (3.92) on $I$ (derivative relative to $I$), and every solution $y$ of (3.92) on $I$ with $y(t_0) = x_0$ equals it at every $t \in I$. The integral is Mathlib's interval integral of an $\mathbb{R}^n$-valued function; it only uses $\Phi(t,s)$ for $s$ between $t_0$ and $t$, hence in $I$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 84, Theorem 3.12

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

namespace TeschlODE.Linear

/-- Teschl, Theorem 3.12 (p. 84), variation of constants (3.97): for `A ∈ C(I, ℝ^{n×n})`,
`g ∈ C(I, ℝⁿ)` and the principal matrix solution `Φ` of `ẋ = A(t) x` on `I`, the function
`x(t) = Φ(t, t₀) x₀ + ∫_{t₀}^{t} Φ(t, s) g(s) ds` solves the inhomogeneous system (3.92)
`ẋ = A(t) x + g(t)` on `I` with `x(t₀) = x₀`, and every solution of that initial value problem
coincides with it on `I`. -/
theorem variation_of_constants {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (g : ℝ → Fin n → ℝ) (hg : ContinuousOn g I)
    (Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ) (hΦ : IsPrincipalMatrixSolution A I Φ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    (∀ t ∈ I, HasDerivWithinAt
        (fun τ => Matrix.mulVec (Φ τ t₀) x₀ + ∫ s in t₀..τ, Matrix.mulVec (Φ τ s) (g s))
        (Matrix.mulVec (A t) (Matrix.mulVec (Φ t t₀) x₀ +
          ∫ s in t₀..t, Matrix.mulVec (Φ t s) (g s)) + g t) I t) ∧
    (∀ y : ℝ → Fin n → ℝ,
      (∀ t ∈ I, HasDerivWithinAt y (Matrix.mulVec (A t) (y t) + g t) I t) → y t₀ = x₀ →
      ∀ t ∈ I, y t = Matrix.mulVec (Φ t t₀) x₀ + ∫ s in t₀..t, Matrix.mulVec (Φ t s) (g s)) := by sorry

end TeschlODE.Linear
