-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_example_4_2
-- name    : ScenarioReduction.TernaryTree.example_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:11:29.204443+00:00
-- url     : https://prove2.me/theorems/31f9fa7f-02fa-421a-acd9-dadd54d39e1e
-- title:
--   Example 4.2 — ternary tree with $K = 6$: $D^{min}_n = 0.7\,\frac{N-n}{N}$ for $162 \le n < 729$
-- statement:
--   Consider the regular ternary scenario tree with $K = 6$, $N = 3^6 = 729$ scenarios of equal probability $p_i = 1/N$, widths
--
--   $$
--   (\delta^1, \dots, \delta^6) = (0.7,\ 0.9,\ 1.2,\ 1.5,\ 2.6,\ 3.3),
--   $$
--
--   and cost $c(\omega_i, \omega_j) = \|\omega_i - \omega_j\|_\infty$. Then for each $n \in \mathbb{N}$ with $\frac{2N}{9} = 162 \le n < N$,
--
--   $$
--   D^{min}_n = \min\{D_J : \#J = N - n\} = 0.7\,\frac{N - n}{N},
--   $$
--
--   and the minimum is attained.
--
--   This is the ternary test instance of the paper's numerical section; Proposition 3.2 applies with $k_0 = 1$, and the instance shows that the proposition's hypotheses can be met.
--
--   **Formalization Note** The minimum is stated as `IsLeast` of the set of values $D_J$ over all $J$ with $\#J = 729 - n$ and a nonempty complement.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 199, Example 4.2

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem example_4_2 (δ : ℕ → ℝ)
    (hδ : δ 1 = 0.7 ∧ δ 2 = 0.9 ∧ δ 3 = 1.2 ∧ δ 4 = 1.5 ∧ δ 5 = 2.6 ∧ δ 6 = 3.3)
    (n : ℕ) (hn : 162 ≤ n) (hnN : n < 729) :
    IsLeast {x : ℝ | ∃ (J : Finset (Fin 6 → Fin 3)) (hJ : Jᶜ.Nonempty), J.card = 729 - n ∧
        x = redCost (fun _ => 1 / (729 : ℝ))
          (fun i j => ‖scenario δ i - scenario δ j‖) J hJ}
      (0.7 * ((729 : ℝ) - n) / 729) := by sorry

end ScenarioReduction.TernaryTree
