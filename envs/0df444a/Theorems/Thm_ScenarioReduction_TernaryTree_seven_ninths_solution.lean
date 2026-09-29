-- Prove2me | Theorems.Thm_ScenarioReduction_TernaryTree_seven_ninths_solution
-- name    : ScenarioReduction.TernaryTree.seven_ninths_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:12:09.719921+00:00
-- url     : https://prove2.me/theorems/05f5ab51-8b0c-47f8-94ad-107f48eed95b
-- title:
--   Proposition 3.2 (7/9-solution) — $D^{min}_n = \frac{N-n}{N}\,\delta^{k_0}$ for $\frac29 N \le n < N$ on a regular ternary tree
-- statement:
--   Let a regular ternary scenario tree with $N = 3^K$ scenarios $\omega_i \in \mathbb{R}^{K+1}$ and $K \ge 3$ be given: $\omega_i^k = \sum_{j=0}^{k} \delta^j_{i_j}$ with $\delta^j_{i_j} = (i_j - 2)\delta^j$, widths $\delta^1, \dots, \delta^K \ge 0$ and $\delta^0 = 0$. All scenarios have probability $p_i = 1/N$, and the cost is the maximum norm $c(\omega_i, \omega_j) = \|\omega_i - \omega_j\|_\infty$. Let
--
--   $$
--   k_0 \in \arg\min_{1 \le k \le K} \delta^k \quad\text{with}\quad k_0 \le K - 2, \qquad \max\{\delta^{k_0+1}, \delta^{k_0+2}\} \le 2\delta^{k_0}.
--   $$
--
--   Then
--
--   1. the distance between any two distinct scenarios is at least $\delta^{k_0}$;
--   2. there is a set $J_{**}$ of $\tfrac79 N$ scenarios each of which has a partner outside $J_{**}$ at distance exactly $\delta^{k_0}$ (giving $\tfrac79 N$ distinct pairs at distance $\delta^{k_0}$);
--   3. for each $n \in \mathbb{N}$ with $\tfrac29 N \le n < N$,
--
--   $$
--   D^{min}_n = \min\{D_J : \#J = N - n\} = \frac{N - n}{N}\,\delta^{k_0}, \tag{21}
--   $$
--
--   where $D_J = \sum_{i \in J} p_i \min_{j \notin J} \|\omega_i - \omega_j\|_\infty$, and the minimum is attained.
--
--   Eq. (21) gives an exact optimal value for the NP-hard optimal scenario-reduction problem (8) on a whole family of instances, which the paper uses to benchmark its heuristics.
--
--   **Formalization Note** The paper's claim "there are $\tfrac79 N$ distinct pairs of scenarios such that the distance between the members of each pair is exactly $\delta^{k_0}$" is false as an exact count of all such pairs (for $K = 3$ and $\delta = (1,1,1)$ there are 130 such unordered pairs, not 21). Conclusion 2 states what the proof constructs: $\tfrac79 N$ pairs, one for each scenario of $J_{**}$, each pairing it with a scenario outside $J_{**}$. The standing assumption $\delta^k \ge 0$ ($\delta^k \in \mathbb{R}_+$, p. 196) is a hypothesis. $\tfrac29 N \le n$ is written $2 \cdot 3^K \le 9n$ and $\tfrac79 N$ as $7 \cdot 3^{K-2}$. The minimum in (21) is stated as `IsLeast` of the set of all values $D_J$, $\#J = N - n$, so it asserts attainment.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 198, Proposition 3.2, eq. (21)

import Mathlib
import Definitions.Def_ScenarioReduction_TernaryTree_scenario
import Definitions.Def_ScenarioReduction_TernaryTree_redCost

namespace ScenarioReduction.TernaryTree

theorem seven_ninths_solution (K : ℕ) (hK : 3 ≤ K) (δ : ℕ → ℝ)
    (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (hk0K : k0 ≤ K - 2) (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 3, σ ≠ τ → δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jss : Finset (Fin K → Fin 3), Jss.card = 7 * 3 ^ (K - 2) ∧
      ∀ j ∈ Jss, ∃ i ∉ Jss, ‖scenario δ i - scenario δ j‖ = δ k0) ∧
    (∀ n : ℕ, 2 * 3 ^ K ≤ 9 * n → n < 3 ^ K →
      IsLeast {x : ℝ | ∃ (J : Finset (Fin K → Fin 3)) (hJ : Jᶜ.Nonempty), J.card = 3 ^ K - n ∧
          x = redCost (fun _ => 1 / (3 : ℝ) ^ K)
            (fun i j => ‖scenario δ i - scenario δ j‖) J hJ}
        (((3 : ℝ) ^ K - n) / 3 ^ K * δ k0)) := by sorry

end ScenarioReduction.TernaryTree
