-- Prove2me | Theorems.Thm_TeschlODE_Linear_solution_space_and_principal_matrix
-- name    : TeschlODE.Linear.solution_space_and_principal_matrix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:55:38.127415+00:00
-- url     : https://prove2.me/theorems/696f4281-167b-4fce-9673-f48ee39fe31b
-- title:
--   Theorem 3.10 — solutions form an n-dimensional space; the principal matrix solution
-- statement:
--   Let $I \subseteq \mathbb{R}$ be a nonempty interval and $A \in C(I, \mathbb{R}^{n\times n})$. Then the solutions of $\dot x = A(t)x$ on $I$ form an $n$-dimensional vector space, and there is a matrix-valued solution $\Phi(t,t_0)$ such that the solution with $x(t_0)=x_0$ is
--   $$x(t) = \Phi(t,t_0)\,x_0, \qquad t, t_0 \in I.$$
--
--   The matrix $\Phi$ is the principal matrix solution (3.83); it is the object in terms of which the rest of the chapter (variation of constants, Floquet theory) is phrased.
--
--   **Formalization Note.** "Form an $n$-dimensional vector space" is stated as three facts about solutions restricted to $I$: linear combinations of solutions are solutions; there are $n$ solutions $\psi_1,\dots,\psi_n$ whose restrictions to $I$ are linearly independent; every solution equals $\sum_j c_j\psi_j$ on $I$ for some coefficients $c$. The matrix part gives a $\Phi$ satisfying `IsPrincipalMatrixSolution A I Φ` and representing every solution as $x(t) = \Phi(t,t_0)x(t_0)$ for $t_0, t \in I$. Nonemptiness of $I$ is the book's implicit assumption (for $I = \emptyset$ the space is $0$-dimensional).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 82, Theorem 3.10

import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution
import Definitions.Def_TeschlODE_Linear_IsPrincipalMatrixSolution

namespace TeschlODE.Linear

/-- Teschl, Theorem 3.10 (p. 82): the solutions of (3.79) on the interval `I` form an
`n`-dimensional vector space (closed under linear combinations, with a basis of `n` solutions
whose restrictions to `I` are linearly independent and span every solution on `I`), and there
is a matrix-valued solution `Φ(t, t₀)` (the principal matrix solution) such that the solution
with `x(t₀) = x₀` is `Φ(t, t₀) x₀` on `I`. -/
theorem solution_space_and_principal_matrix {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (I : Set ℝ) (hI : I.OrdConnected) (hIne : I.Nonempty) (hA : ContinuousOn A I) :
    (∀ (x y : ℝ → Fin n → ℝ) (a b : ℝ), IsSolution A I x → IsSolution A I y →
      IsSolution A I (a • x + b • y)) ∧
    (∃ ψ : Fin n → ℝ → Fin n → ℝ, (∀ j, IsSolution A I (ψ j)) ∧
      LinearIndependent ℝ (fun j (t : I) => ψ j t) ∧
      ∀ x : ℝ → Fin n → ℝ, IsSolution A I x →
        ∃ c : Fin n → ℝ, ∀ t ∈ I, x t = ∑ j, c j • ψ j t) ∧
    (∃ Φ : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ, IsPrincipalMatrixSolution A I Φ ∧
      ∀ t₀ ∈ I, ∀ x : ℝ → Fin n → ℝ, IsSolution A I x →
        ∀ t ∈ I, x t = Matrix.mulVec (Φ t t₀) (x t₀)) := by sorry

end TeschlODE.Linear
