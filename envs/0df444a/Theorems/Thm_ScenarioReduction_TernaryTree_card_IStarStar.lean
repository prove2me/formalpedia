-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_card_IStarStar
-- name    : ScenarioReduction.TernaryTree.card_IStarStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:10:22.461722+00:00
-- url     : https://prove2.me/theorems/e63d72f3-febe-4e02-96f4-3d2b13ba5e98
-- title:
--   Proposition 3.2, proof — $\#I_{**} = \frac29 N$ and $\#J_{**} = \frac79 N$
-- statement:
--   Let $K \ge 3$, $N = 3^K$, and $1 \le k_0 \le K - 2$. Let $I_{**}$ be the set of scenarios of a regular ternary tree that take the middle branch at level $k_0$ and outer branches at levels $k_0+1, k_0+2$, or an outer branch at level $k_0$ and middle branches at levels $k_0+1, k_0+2$, and let $J_{**} = \{1, \dots, N\} \setminus I_{**}$. Then
--
--   $$
--   \#I_{**} = 3^{k_0-1} \cdot 6 \cdot 3^{K-k_0-2} = \tfrac29\,3^K = \tfrac29 N, \qquad \#J_{**} = N - \#I_{**} = \tfrac79 N.
--   $$
--
--   The count shows that the reduction kept at $I_{**}$ has exactly $\tfrac29 N$ scenarios, the threshold of Proposition 3.2.
--
--   **Formalization Note** $\tfrac29 N$ and $\tfrac79 N$ are written as $2 \cdot 3^{K-2}$ and $7 \cdot 3^{K-2}$ (natural-number exponents, $K \ge 3$). $I_{**}$ is defined by branch indices, not by the values of the increments; see the definition `IStarStar`.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), pp. 198–199, proof of Proposition 3.2, definition of I_** and the display on p. 199

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_IStarStar

namespace ScenarioReduction.TernaryTree

theorem card_IStarStar (K k0 : ℕ) (hk0 : 1 ≤ k0) (hk0K : k0 ≤ K - 2) (hK : 3 ≤ K) :
    (IStarStar K k0).card = 2 * 3 ^ (K - 2) ∧ (IStarStar K k0)ᶜ.card = 7 * 3 ^ (K - 2) := by sorry

end ScenarioReduction.TernaryTree
