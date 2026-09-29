-- Prove2me | Theorems.Thm_VectorSpaceOpt_dual_approximation
-- name    : VectorSpaceOpt.dual_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:25:12.198852+00:00
-- url     : https://prove2.me/theorems/dae7e59b-2102-413e-9022-fde595f88089
-- title:
--   The dual approximation problem: minimum norm subject to inner product constraints
-- statement:
--   Let $H$ be a real Hilbert space, let $y_1, \dots, y_n$ be **linearly independent** vectors in $H$, and let $c_1, \dots, c_n$ be real constants. Consider the vectors $x \in H$ satisfying the $n$ constraints
--
--   $$\langle x,\, y_1\rangle = c_1, \quad \langle x,\, y_2\rangle = c_2, \quad \dots, \quad \langle x,\, y_n\rangle = c_n,$$
--
--   which form a linear variety of **codimension $n$** — a translate of the orthogonal complement of $\operatorname{span}\{y_1, \dots, y_n\}$. Among all such $x$, let $x_0$ have minimum norm. Then $x_0$ is a linear combination of the $y_i$,
--
--   $$x_0 = \sum_{i=1}^{n} \beta_i\, y_i,$$
--
--   and the coefficients $\beta_1, \dots, \beta_n$ are determined by the $n \times n$ linear system
--
--   $$\langle y_1, y_i\rangle\, \beta_1 + \langle y_2, y_i\rangle\, \beta_2 + \cdots + \langle y_n, y_i\rangle\, \beta_n = c_i, \qquad i = 1, \dots, n,$$
--
--   whose coefficient matrix is the Gram matrix of the $y_i$. The minimum-norm solution exists and is unique.
--
--   The significance is the reduction. The feasible set is infinite-dimensional whenever $H$ is, so there is no general reason to expect a finite computation; but the minimum-norm point is orthogonal to the orthogonal complement, hence lies in the $n$-dimensional span of the $y_i$, and the problem collapses to $n$ equations in $n$ unknowns. The system is the **dual** counterpart of the normal equations: there the constraints identified the subspace and the inner products were data, here the inner products are the constraints. The source applies it to minimum-energy control, where the $y_i$ encode terminal conditions on a dynamical system and the norm is control energy.
--
--   **Formalization Note.** The statement exhibits the coefficient family $\beta$ and asserts four things about it: that it solves the Gram system, that the resulting $x_0$ is feasible, that $x_0$ is of minimum norm among feasible vectors, and that any feasible vector matching its norm equals it. Together the last two are the uniqueness of the minimum-norm solution.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.10, Theorem 2, pp. 65–66

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem dual_approximation {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℝ y) (c : Fin n → ℝ) :
    ∃ β : Fin n → ℝ,
      (∀ i, ∑ j, β j * ⟪y j, y i⟫ = c i) ∧
      (∀ i, ⟪∑ j, β j • y j, y i⟫ = c i) ∧
      (∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ‖∑ j, β j • y j‖ ≤ ‖z‖) ∧
      (∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ‖z‖ ≤ ‖∑ j, β j • y j‖ →
        z = ∑ j, β j • y j) := by sorry

end VectorSpaceOpt
