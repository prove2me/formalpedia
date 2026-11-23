-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_4_2
-- name    : RobustInventory.SingleStation.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:30:05.778471+00:00
-- url     : https://prove2.me/theorems/339cb3e5-3e91-4c22-9615-d32ec6391ac3
-- title:
--   Theorem 4.2, p. 158: optimal robust policy and cost on a tree network (corrected: plant links in the objective of (32))
-- statement:
--   **Theorem 4.2 (Optimal Robust Policy).** Consider a supply chain on a tree network with $N$ echelons and horizon $T$. Echelon $k$ orders $D_k(t)\ge0$ from its only supplier and has costs $c_k>0$, $K_k\ge0$, $h_k\ge0$, $p_k>c_k$; $O(k)$ is its set of sinks. Each sink $s$ has demand data $\bar W_s$, $\hat W_s$, $\Gamma_s$ as in §3.1, and $A_s(t)$ is the corresponding value of LP (13), with $A_s(-1)=0$. Put
--   $$W'_{s,k}(t)=\bar W_s(t)+\frac{p_k-h_k}{p_k+h_k}(A_s(t)-A_s(t-1)),\qquad E=\sum_{k=1}^{N}\frac{2p_kh_k}{p_k+h_k}\sum_{t=0}^{T-1}\sum_{s\in O(k)}A_s(t).$$
--   Let $X'_k(t+1)=X'_k(t)+D_k(t)-\sum_{s\in O(k)}W'_{s,k}(t)$, $X'_k(0)=X_k(0)$, and let
--   $$V'(D)=\sum_{t<T}\sum_{k=1}^{N}\big[K_k\mathbf 1_{\{D_k(t)>0\}}+c_kD_k(t)+\max(h_kX'_k(t+1),-p_kX'_k(t+1))\big].$$
--   Orders are feasible if they are nonnegative and, at each installation that supplies others, the orders made to it do not exceed its stock on hand.
--
--   1. For every feasible order array $D$, every completion $(Y,q,r)$ feasible in (32) has objective at least $V'(D)+E$, and some completion attains this value.
--   2. **(a)** An order array is the order part of an optimal solution of (32) if and only if it minimizes $V'$ over the feasible arrays. In particular the optimal orders of every echelon $k$ are those of the supply chain in which it sees $W'_{s,k}$ at each sink $s\in O(k)$.
--   3. **(b)** For an optimal solution of (32) and a minimizer $D'$ of $V'$, the optimal robust cost equals $V'(D')+E$.
--
--   The robust supply chain problem thus has the structure of a nominal one, at a known extra cost, for every tree topology.
--
--   **Formalization Note** The objective of (32) is summed over all $N$ echelons with their supply links. As printed, $\sum_k\sum_{i\in N(k)}$ omits the links from the outside plants, and (b) is then false: for $N=T=1$, $X_1(0)=0$, $\bar W=\hat W=10$, $\Gamma=1$, $c=1$, $h=p=2$, $K=0$ the printed objective is $0$, while $V'(D')+E=30$. The coupling constraint is not imposed at sinks, which may backlog. No sign is assumed for the initial stock on hand of a supplier; feasibility makes it nonnegative.
--
--   Differences from the source:
--   - correction: objective Σ_t Σ_k Σ_{i∈N(k)} of (32), which omits the links from the outside plants → sum over all N echelons, each with its supply link, and D ≥ 0 on plant links; reason: notation slip: Y_i is constrained for all i, §4.1 gives every echelon its costs and (b) sums over k = 1, …, N; as printed, N = T = 1, X_1(0) = 0, W̄ = Ŵ = 10, Γ = 1, c = 1, h = p = 2, K = 0 has optimal objective 0, while the right side of (b) is 30. No case is excluded
--   - reading: coupling constraint (31) printed "for all k" → (31) for every installation that is not a sink; reason: N(k) is empty at a sink, where the constraint would forbid the backlog allowed by §4.1; p. 157 claims I_k(t) ≥ 0 only for installations that supply others
--   - reading: "the supply chain subject to the modified, deterministic demand" W′_{s,k} → each echelon k sees its own W′_{s,k} in its stock and cost, and the coupling constraint is that of (32); reason: (34) depends on k and p. 159 says echelons see different demands; the stock on hand in (31) does not depend on demand
--   - reading: A_s(t) = q*_s(t)Γ_s(t) + Σ r*_s(τ, t) for the optimal q*, r* of (32) → A_s(t) is the optimal value of LP (13) for sink s; reason: the optimal q*, r* need not be unique (h = 0); §4.1 keeps the conventions of §3.1
--   - reading: "tree networks", with sources supplied by outside plants → an acyclic supplier map with one supplier per installation, several sources allowed; reason: §4.1 speaks of the sources in the plural and calls one source with one sink the special case of a series system
--   - reading: "the optimal policy … for echelon k" → an equivalence between whole optimal order arrays; reason: the echelons are coupled by (31); the equivalence of arrays gives each echelon component
--   - encoding: link variables D_ki(t), link costs c_ki, K_ki and binary V_ki(t) with a big M → one order D_i(t) per installation, priced with the costs c_i, K_i of echelon i, and the fixed-cost indicator; reason: each installation has one supplier, §4.1 gives each echelon its own (c_k, K_k, h_k, p_k), and for M large enough the problems agree
--   - generalization: (b) equates the two optimal costs → also the identity of the least robust cost and modified cost plus the extra term at every feasible order array; reason: specializes to (b) at optimal arrays, as in the published Theorem 3.2
--   - generalization: the demand is always nonnegative, ŵ_k ≤ w̄_k (p. 156) → no sign condition on W̄_s or W′_{s,k}; reason: the statement holds without it, and nonnegative demand is a special case
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 158 (PDF 9), Theorem 4.2 and Eq. (34); p. 157 (PDF 8), formulation (32)

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkRobust

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 4.2, p. 158, for a tree network.
1. (b), for every feasible order array `D`: the least objective of (32) at `D` is the cost of
   `D` under the modified demands (34) plus `extraCost`.
2. (a): `D` is the order part of an optimal solution of (32) iff it is optimal for the supply
   chain in which every echelon `k` sees the demands `W'_{s,k}` at the sinks `s ∈ O(k)`.
3. (b): the optimal cost of (32) is the optimal cost of that supply chain plus `extraCost`. -/
theorem theorem_4_2 (G : Network) :
    (∀ D : Fin G.N → ℕ → ℝ, G.OrdersFeasible D →
      (∀ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r →
        G.modifiedCost D + G.extraCost ≤ G.robustObjective D Y) ∧
      ∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.RobustFeasible D Y q r ∧
        G.robustObjective D Y = G.modifiedCost D + G.extraCost) ∧
    (∀ D : Fin G.N → ℕ → ℝ,
      (∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ), G.IsRobustOptimal D Y q r) ↔
        G.IsModifiedOptimal D) ∧
    ∀ (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) (D' : Fin G.N → ℕ → ℝ),
      G.IsRobustOptimal D Y q r → G.IsModifiedOptimal D' →
        G.robustObjective D Y = G.modifiedCost D' + G.extraCost := by sorry

end RobustInventory.SingleStation.Supplement
