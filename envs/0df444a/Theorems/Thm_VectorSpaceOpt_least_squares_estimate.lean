-- Prove2me | Theorems.Thm_VectorSpaceOpt_least_squares_estimate
-- name    : VectorSpaceOpt.least_squares_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:27:03.919935+00:00
-- url     : https://prove2.me/theorems/a721682b-317d-4fc4-b3b8-d2eceb6d396c
-- title:
--   The least-squares estimate
-- statement:
--   Suppose $y$ is an $m$-vector of data and $W$ an $m \times n$ matrix with **linearly independent columns**, where $n < m$. Since the system $y = W\beta$ is overdetermined, one seeks instead the $\beta$ best fitting it in the least-squares sense, minimizing the Euclidean norm of the residual $\|y - W\beta\|$.
--
--   There is a **unique** minimizer, and it is
--
--   $$\hat\beta = (W^\top W)^{-1} W^\top y.$$
--
--   The problem is not statistical: it amounts to approximating $y$ by a vector in the column space of $W$, so existence and uniqueness are the projection theorem, and the normal equations $W^\top W \beta = W^\top y$ are the orthogonality condition — the Gram matrix of the columns of $W$ is exactly $W^\top W$, nonsingular precisely because those columns are independent.
--
--   **Formalization Note.** The squared norm is written as the explicit sum $\sum_i (y_i - (W\beta)_i)^2$, avoiding any ambiguity about which norm a pi type carries. Minimality and uniqueness are stated as separate conjuncts about the named vector $\hat\beta$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.3, Theorem 1, p. 83

import Mathlib
open Matrix

namespace VectorSpaceOpt

theorem least_squares_estimate {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (hW : LinearIndependent ℝ (fun j : Fin n => fun i : Fin m => W i j))
    (y : Fin m → ℝ) (βls : Fin n → ℝ)
    (hβls : βls = (Wᵀ * W)⁻¹.mulVec (Wᵀ.mulVec y)) :
    (∀ β : Fin n → ℝ,
      ∑ i, (y i - W.mulVec βls i) ^ 2 ≤ ∑ i, (y i - W.mulVec β i) ^ 2) ∧
    (∀ β : Fin n → ℝ,
      (∀ β' : Fin n → ℝ,
        ∑ i, (y i - W.mulVec β i) ^ 2 ≤ ∑ i, (y i - W.mulVec β' i) ^ 2) →
      β = βls) := by sorry

end VectorSpaceOpt
