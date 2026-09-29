-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_partner_in_IStarStar
-- name    : ScenarioReduction.TernaryTree.partner_in_IStarStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:10:53.774683+00:00
-- url     : https://prove2.me/theorems/d50ef6ff-e8f3-4a7d-99a5-4ce704ee028b
-- title:
--   Proposition 3.2, proof — every $j \in J_{**}$ has a partner $i \in I_{**}$ at distance exactly $\delta^{k_0}$
-- statement:
--   Let a regular ternary scenario tree with $N = 3^K$ scenarios and $K \ge 3$ be given, with widths $\delta^1, \dots, \delta^K \ge 0$. Let $k_0 \in \arg\min_{1 \le k \le K} \delta^k$ with $k_0 \le K - 2$ and $\max\{\delta^{k_0+1}, \delta^{k_0+2}\} \le 2\delta^{k_0}$. Let $I_{**}$ be the index set of the proof of Proposition 3.2 and $J_{**}$ its complement. Then for each $j \in J_{**}$ there exists $i \in I_{**}$ with
--
--   $$
--   \|\omega_i - \omega_j\|_\infty = \delta^{k_0}.
--   $$
--
--   Together with the distance lower bound this shows that keeping exactly the scenarios of $I_{**}$ costs $D_{J_{**}} = \frac{\#J_{**}}{N}\delta^{k_0} = \frac79\delta^{k_0}$, which attains the lower bound.
--
--   **Formalization Note** $I_{**}$ is defined by branch indices; see the definition `IStarStar`. The hypotheses are those of Proposition 3.2 together with the standing assumption $\delta^k \ge 0$ of §3.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 199, proof of Proposition 3.2

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_IStarStar

namespace ScenarioReduction.TernaryTree

theorem partner_in_IStarStar (K : ℕ) (hK : 3 ≤ K) (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (hk0K : k0 ≤ K - 2) (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStarStar K k0, ∃ i ∈ IStarStar K k0, ‖scenario δ i - scenario δ j‖ = δ k0 := by sorry

end ScenarioReduction.TernaryTree
