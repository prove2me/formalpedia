-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_2_1
-- name    : RobustInventory.SingleStation.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:26:16.553806+00:00
-- url     : https://prove2.me/theorems/5ade87ad-8374-4f95-bed3-17468e66d59f
-- title:
--   Theorem 2.1, p. 152: the linear program (2) is the robust counterpart of the uncertain linear program (1)
-- statement:
--   **Theorem 2.1 (Bertsimas and Sim).** Consider a linear program $\min\{c'x:Ax\le b,\ l\le x\le u\}$ with $m$ rows and $n$ columns, in which the coefficients indexed by $J$ are uncertain: $a_{ij}=\bar a_{ij}+\hat a_{ij}z_{ij}$ with $\hat a_{ij}\ge0$, $|z_{ij}|\le1$, $\sum_{(i,j)\in J}|z_{ij}|\le\Gamma$, and $a_{ij}=\bar a_{ij}$ off $J$, where $\Gamma\ge0$. Let $\mathcal A$ be the set of these matrices. Problem (1) minimizes $c'x$ over $l\le x\le u$ with $Ax\le b$ for all $A\in\mathcal A$. Its counterpart (2) is
--   $$\begin{aligned}\min\ &c'x\\ \text{s.t. }&\textstyle\sum_j\bar a_{ij}x_j+q_i\Gamma+\sum_{j:(i,j)\in J}r_{ij}\le b_i&&\forall i,\\ &q_i+r_{ij}\ge\hat a_{ij}y_j&&\forall(i,j)\in J,\\ &-y\le x\le y,\quad l\le x\le u,\quad q,r,y\ge0 .\end{aligned}$$
--
--   1. A vector $x$ is feasible for (1) if and only if some $(q,r,y)$ makes $(x,q,r,y)$ feasible for (2).
--   2. A vector $x$ is optimal for (1) if and only if some $(q,r,y)$ makes $(x,q,r,y)$ optimal for (2).
--   3. The two problems have the same set of objective values, hence the same optimal value.
--
--   The robust version of a linear program is thus again a linear program. The inventory formulations of §3 and §4 are instances of this reformulation.
--
--   **Formalization Note** One budget covers all of $J$, yet each row receives all of $\Gamma$, because each row is imposed for every matrix in $\mathcal A$. Rows without uncertain coefficients and an empty $J$ are allowed.
--
--   Differences from the source:
--   - reading: (2) is "the robust, linear counterpart" of the uncertain problem → same feasible x after projection, same optimal x, same set of objective values; reason: this is what "counterpart" means in the proof, which reinjects the dual (4) into (1)
--   - encoding: a_ij in [ā_ij − â_ij, ā_ij + â_ij] with Σ_J |a_ij − ā_ij|/â_ij ≤ Γ → a_ij = ā_ij + â_ij z_ij with |z_ij| ≤ 1, Σ_J |z_ij| ≤ Γ and z = 0 off J; reason: the paper's scaled deviation z_ij; it avoids division by â_ij = 0, and only the parameters indexed by J are uncertain
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 152 (PDF 3), §2.2, Theorem 2.1 with problems (1) and (2)

import Definitions.Def_RobustInventory_SingleStation_Supplement_BudgetedLP

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 2.1, p. 152: the linear program (2) is the robust counterpart of (1).
1. `x` is feasible for (1) iff it extends to a feasible point of (2).
2. `x` is optimal for (1) iff it is the `x`-part of an optimal point of (2).
3. The two problems have the same set of objective values, hence the same optimal value. -/
theorem theorem_2_1 {m n : ℕ} (P : BudgetedLP m n) :
    (∀ x, P.RobustFeasible x ↔ ∃ q r y, P.CounterpartFeasible x q r y) ∧
    (∀ x, P.IsRobustOptimal x ↔ ∃ q r y, P.IsCounterpartOptimal x q r y) ∧
    {v : ℝ | ∃ x, P.RobustFeasible x ∧ v = P.cost x} =
      {v : ℝ | ∃ x q r y, P.CounterpartFeasible x q r y ∧ v = P.cost x} := by sorry

end RobustInventory.SingleStation.Supplement
