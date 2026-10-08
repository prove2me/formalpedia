-- Prove2me | Theorems.Thm_ShapleyScarf_Balanced_exists_permutation_le_B_of_doublyStochastic_le
-- name    : ShapleyScarf.Balanced.exists_permutation_le_B_of_doublyStochastic_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:26.295098+00:00
-- url     : https://prove2.me/theorems/2527c7b0-eb7f-4b4f-aee3-7697074acd50
-- title:
--   Section 4 — round a feasible doubly stochastic matrix to a permutation
-- statement:
--   Let $D$ be a doubly stochastic matrix in a nonempty finite housing market. Fix a payoff vector $x$. If each entry of $D$ is at most the corresponding entry of the grand-coalition acceptability matrix $B_N(x)$, then there is an $N$-permutation matrix $P_N$ such that
--   $$
--   P_{N|ij}\le B_{N|ij}(x)\qquad\text{for every }i,j\in N.
--   $$
--
--   In particular, the payoff vector $x$ belongs to $V(N)$. This isolates the existence statement at the end of the paper's matrix argument.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; pp. 110–111 of the source printing, Section 4, proof of the Theorem, final matrix step

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem exists_permutation_le_B_of_doublyStochastic_le
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (x : N → ℝ) (D : Matrix N N ℝ)
    (hD : D ∈ doublyStochastic ℝ N)
    (hDB : ∀ i j, D i j ≤ acceptableMatrix A Finset.univ x i j) :
    ∃ P : Matrix N N ℝ, IsSPermutation Finset.univ P ∧
      ∀ i j, P i j ≤ acceptableMatrix A Finset.univ x i j := by sorry

end ShapleyScarf.Balanced
