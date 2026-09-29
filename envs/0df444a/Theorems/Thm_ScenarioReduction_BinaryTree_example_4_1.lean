-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_example_4_1
-- name    : ScenarioReduction.BinaryTree.example_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:07:28.897924+00:00
-- url     : https://prove2.me/theorems/4522ef60-d8ca-4023-ab91-03c40b2ead99
-- title:
--   Example 4.1: binary tree with $K=10$; Proposition 3.1 applies with $k_0=1$ and $D^{min}_n=\frac{N-n}{N}$ for $256\le n<1024$
-- statement:
--   Let $K=10$, $N=2^{10}=1024$, $p_i=1/N$, and consider the regular binary scenario tree with level parameters
--
--   $$(\delta^1,\dots,\delta^{10})=(0.5,\,0.6,\,0.7,\,0.9,\,1.1,\,1.3,\,1.6,\,1.9,\,2.3,\,2.7).$$
--
--   Then the hypotheses of Proposition 3.1 hold with $k_0=1$ (namely $\delta^1\le\delta^k$ for all $k$, $k_0\le K-2$, and $\max\{\delta^2,\delta^3\}\le2\delta^1$), and for each $n$ with $\frac N4=256\le n<N$
--
--   $$D^{min}_n=\min\{D_J:\#J=N-n\}=\frac{N-n}{N}.$$
--
--   The example is the first test tree of the paper's numerical section, where the known optimal value is compared with the output of the reduction heuristics. It also shows that the hypotheses of Proposition 3.1 are satisfiable.
--
--   **Formalization Note** The parameters are any $\delta:\mathbb N\to\mathbb R$ with the ten listed values at levels $1,\dots,10$; other values are not used. The minimum is stated as `IsLeast`, so it includes attainment. Distances are in the maximum norm, as in Section 3.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 199, Example 4.1

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost

namespace ScenarioReduction.BinaryTree

theorem example_4_1 (δ : ℕ → ℝ) (h1 : δ 1 = 0.5) (h2 : δ 2 = 0.6) (h3 : δ 3 = 0.7)
    (h4 : δ 4 = 0.9) (h5 : δ 5 = 1.1) (h6 : δ 6 = 1.3) (h7 : δ 7 = 1.6) (h8 : δ 8 = 1.9)
    (h9 : δ 9 = 2.3) (h10 : δ 10 = 2.7) :
    ((∀ k ∈ Finset.Icc 1 10, δ 1 ≤ δ k) ∧ (1 : ℕ) ≤ 10 - 2 ∧ max (δ 2) (δ 3) ≤ 2 * δ 1) ∧
    ∀ n : ℕ, 256 ≤ n → n < 1024 →
      IsLeast {v : ℝ | ∃ J : Finset (Fin 10 → Fin 2), J.card = 2 ^ 10 - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        ((1024 - n : ℝ) / 1024) := by sorry

end ScenarioReduction.BinaryTree
