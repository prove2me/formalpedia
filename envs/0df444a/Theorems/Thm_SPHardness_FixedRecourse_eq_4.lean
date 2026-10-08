-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_eq_4
-- name    : SPHardness.FixedRecourse.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:35.959185+00:00
-- url     : https://prove2.me/theorems/55e2f00f-8d2c-4e41-b60a-b2832abe788d
-- title:
--   Equation (4), pp. 4–5 — inverse Vandermonde column-sum bound
-- statement:
--   Let $\alpha\in\mathbb R^k_+$ and $0\le\beta\le\sum_j\alpha_j$. For the budgets $\gamma_i=\beta+i/(k+1)$ and the matrix $F_{ic}=\gamma_i^{k-c}$, $F$ is invertible and every column of its inverse satisfies
--   $$\sum_{r=0}^k |(F^{-1})_{rc}|\le (\|\alpha\|_1+2)^k(k+1)^k.$$
--   The column sums are the operator $1$-norm used in the perturbation estimate (6).
--
--   **Formalization Note** The paper's displayed determinant product has the sign for ascending columns, while its printed $F$ has descending columns. The statement keeps the needed nonzero determinant.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), pp. 4–5, (4)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem eq_4 {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 ≤ α j) (hβ0 : 0 ≤ β) (hβ : β ≤ ∑ j, α j) :
    (vandermondeF k β).det ≠ 0 ∧
      ∀ c : Fin (k + 1), ∑ r : Fin (k + 1),
        |((vandermondeF k β)⁻¹) r c| ≤
          ((∑ j, α j) + 2) ^ k * (k + 1 : ℝ) ^ k := by sorry
end SPHardness.FixedRecourse
