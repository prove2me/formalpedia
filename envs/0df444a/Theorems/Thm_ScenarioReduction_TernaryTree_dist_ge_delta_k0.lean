-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_dist_ge_delta_k0
-- name    : ScenarioReduction.TernaryTree.dist_ge_delta_k0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:09:15.606546+00:00
-- url     : https://prove2.me/theorems/651a8d3b-b8bf-4fa4-ab89-17c095b0af1b
-- title:
--   Proposition 3.2, proof — distinct scenarios are at max-norm distance $\ge \delta^{k_0}$
-- statement:
--   Let a regular ternary scenario tree of depth $K$ be given, with widths $\delta^1, \dots, \delta^K \ge 0$ and scenarios $\omega_i \in \mathbb{R}^{K+1}$, $i = 1, \dots, N = 3^K$. Let $k_0 \in \arg\min_{1 \le k \le K} \delta^k$. Then for all scenarios $i \ne j$,
--
--   $$
--   \|\omega_i - \omega_j\|_\infty \ge \delta^{k_0}.
--   $$
--
--   This is the lower half of the proof of Proposition 3.2: every deleted scenario costs at least $\delta^{k_0}$ per unit probability.
--
--   **Formalization Note** The statement assumes only the standing assumptions of §3 and that $k_0$ minimizes $\delta$ over $\{1, \dots, K\}$; the remaining hypotheses of Proposition 3.2 ($K \ge 3$, $k_0 \le K-2$, $\max\{\delta^{k_0+1}, \delta^{k_0+2}\} \le 2\delta^{k_0}$) are not needed for this bound and are omitted. Scenarios are index tuples $\sigma, \tau : \mathrm{Fin}\,K \to \mathrm{Fin}\,3$ and the norm on $\mathrm{Fin}(K+1) \to \mathbb{R}$ is the maximum norm.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 198, proof of Proposition 3.2, first display

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario

namespace ScenarioReduction.TernaryTree

theorem dist_ge_delta_k0 (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 3) (hστ : σ ≠ τ) :
    δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by sorry

end ScenarioReduction.TernaryTree
