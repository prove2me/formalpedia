-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_redCost_lower_bound
-- name    : ScenarioReduction.TernaryTree.redCost_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:09:50.745974+00:00
-- url     : https://prove2.me/theorems/cf5e187f-0ad9-4e3f-9879-9f99fdb65818
-- title:
--   Proposition 3.2, proof — $D_J \ge \frac{N-n}{N}\,\delta^{k_0}$ for every $J$ with $\#J = N-n$
-- statement:
--   Let a regular ternary scenario tree of depth $K$ be given, with widths $\delta^1, \dots, \delta^K \ge 0$, $N = 3^K$ scenarios $\omega_i$ of equal probability $p_i = 1/N$, and cost $c(\omega_i, \omega_j) = \|\omega_i - \omega_j\|_\infty$. Let $k_0 \in \arg\min_{1 \le k \le K} \delta^k$ and let $n \in \mathbb{N}$ with $n < N$. Then for each index set $J \subset \{1, \dots, N\}$ with $\#J = N - n$ that leaves at least one scenario,
--
--   $$
--   D_J = \sum_{i \in J} p_i \min_{j \notin J} \|\omega_i - \omega_j\|_\infty \ge \frac{N-n}{N}\,\delta^{k_0}.
--   $$
--
--   This is the lower bound half of eq. (21): no reduction to $n$ scenarios can beat $\frac{N-n}{N}\delta^{k_0}$.
--
--   **Formalization Note** The complement of $J$ is required to be nonempty so that $D_J$ is defined; for $n \ge 1$ this follows from $\#J = N - n$. As in the previous milestone, only the arg-min property of $k_0$ is assumed.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 198, proof of Proposition 3.2, second display

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 3 ^ K) (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty)
    (hcard : J.card = 3 ^ K - n) :
    ((3 : ℝ) ^ K - n) / 3 ^ K * δ k0 ≤
      redCost (fun _ => 1 / (3 : ℝ) ^ K) (fun i j => ‖scenario δ i - scenario δ j‖) J hJ := by sorry

end ScenarioReduction.TernaryTree
