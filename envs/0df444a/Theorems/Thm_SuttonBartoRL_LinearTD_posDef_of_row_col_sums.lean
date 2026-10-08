-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_posDef_of_row_col_sums
-- name    : SuttonBartoRL.LinearTD.posDef_of_row_col_sums
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:47:55.821524+00:00
-- url     : https://prove2.me/theorems/25993bc2-83df-429c-af37-1fdbbdfe06ca
-- title:
--   Positive diagonal, nonpositive off-diagonal, positive row sums and nonnegative column sums imply $y^\top M y > 0$
-- statement:
--   Let $M$ be a real $n \times n$ matrix, not necessarily symmetric, such that
--
--   1. every diagonal entry is positive, $M_{ii} > 0$;
--   2. every off-diagonal entry is nonpositive, $M_{ij} \le 0$ for $i \ne j$;
--   3. every row sum is positive, $\sum_j M_{ij} > 0$;
--   4. every column sum is nonnegative, $\sum_i M_{ij} \ge 0$.
--
--   Then $M$ is positive definite:
--
--   $$y^\top M y > 0 \qquad \text{for every } y \in \mathbb R^n,\ y \ne 0 .$$
--
--   This is the criterion the book's convergence box applies to the key matrix $\mathbf D(\mathbf I - \gamma \mathbf P)$ of linear TD(0), following Sutton (1988, p. 27): the symmetric part $M + M^\top$ is then strictly diagonally dominant with positive diagonal (Varga 1962, p. 23).
--
--   **Formalization Note** The book says the off-diagonal entries of the key matrix are "negative"; they are $-\gamma\mu(s)p(s' \mid s)$, which is zero whenever $p(s' \mid s) = 0$, so the criterion is stated with nonpositive off-diagonal entries, which covers the key matrix. Positive definiteness is in the book's sense for non-symmetric matrices, not Mathlib's `Matrix.PosDef`.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of Convergence of Linear TD(0)", p. 207 (citing Sutton 1988, p. 27, and Varga 1962, p. 23)

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), box "Proof of Convergence of Linear TD(0)", p. 207 (after Sutton 1988,
p. 27, and Varga 1962, p. 23): a real square matrix whose diagonal entries are positive, whose
off-diagonal entries are nonpositive, whose row sums are positive and whose column sums are
nonnegative is positive definite in the sense `yᵀMy > 0` for all `y ≠ 0`. -/
theorem posDef_of_row_col_sums {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hdiag : ∀ i, 0 < M i i) (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, M i j) (hcol : ∀ j, 0 ≤ ∑ i, M i j) :
    IsPosDefNonsym M := by sorry

end SuttonBartoRL.LinearTD
