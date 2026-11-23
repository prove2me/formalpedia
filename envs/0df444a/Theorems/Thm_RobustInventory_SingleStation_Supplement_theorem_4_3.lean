-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_4_3
-- name    : RobustInventory.SingleStation.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:31:00.995106+00:00
-- url     : https://prove2.me/theorems/233046a0-ed44-413a-aa8b-0d15c331f353
-- title:
--   Theorem 4.3, p. 159: optimal policy with link and echelon capacities (corrected: plant links in the objective of (32))
-- statement:
--   **Theorem 4.3 (Optimal Policy with Link and Echelon Capacities).** Consider the tree network of Theorem 4.2, with echelon costs $(c_k,K_k,h_k,p_k)$, sinks $O(k)$ and worst deviations $A_s(t)$ given by LP (13). Let $d_i\in\mathbb R\cup\{+\infty\}$ bound the link into installation $i$ and let $C_k$ be the capacity of echelon $k$. The capacitated robust problem is (32), summed over all echelons, with $D_i(t)\le d_i$ and
--   $$\bar X_k(t+1)+\sum_{s\in O(k)}\Big(q_s(t)\Gamma_s(t)+\sum_{\tau=0}^{t}r_s(\tau,t)\Big)\le C_k\qquad\forall k,\ \forall t<T,$$
--   where $\bar X$ is the nominal echelon stock and $q,r$ are the variables of (32).
--
--   An order array is the order part of an optimal solution of this problem if and only if it is optimal for the supply chain in which echelon $k$ sees the modified demands $W'_{s,k}(t)=\bar W_s(t)+\frac{p_k-h_k}{p_k+h_k}(A_s(t)-A_s(t-1))$, with the same coupling constraints, the same link capacities and, on the modified echelon stock $X'_k$,
--   $$X'_k(t+1)\le C'_k(t+1)=C_k-\frac{2p_k}{p_k+h_k}\sum_{s\in O(k)}A_s(t).$$
--
--   Capacities on links and echelons therefore keep the problem equivalent to a nominal one, with time-varying echelon capacities.
--
--   **Formalization Note** The capacity shift has coefficient $2p_k/(p_k+h_k)$, without $h_k$ in the numerator. The objective of (32) includes the plant links, which its printed double sum omits. With that omission, in the one-echelon example $T=1$, $X_1(0)=0$, $\bar W=\hat W=10$, $\Gamma=1$, $c=1$, $h=p=2$, $K=0$, $C_1=100$, the order $0$ would be robust optimal, although the only nominal optimum under the modified demand is $10$. Neither problem is assumed feasible.
--
--   Differences from the source:
--   - correction: objective Σ_t Σ_k Σ_{i∈N(k)} of (32), which omits the links from the outside plants → sum over all N echelons, each with its supply link, and D ≥ 0 on plant links; reason: the notation slip of (32); as printed, N = T = 1, X_1(0) = 0, W̄ = Ŵ = 10, Γ = 1, c = 1, h = p = 2, K = 0, C_1 = 100 makes D = 0 robust optimal, while the only modified nominal optimum is D = 10. No case is excluded
--   - reading: coupling constraint (31) printed "for all k" → (31) for every installation that is not a sink; reason: N(k) is empty at a sink, where the constraint would forbid the backlog allowed by §4.1; p. 157 claims I_k(t) ≥ 0 only for installations that supply others
--   - reading: "the supply chain subject to the modified, deterministic demand" W′_{s,k} → each echelon k sees its own W′_{s,k} in its stock and cost, and the coupling constraint is that of (32); reason: (34) depends on k and p. 159 says echelons see different demands; the stock on hand in (31) does not depend on demand
--   - reading: A_s(t) = q*_s(t)Γ_s(t) + Σ r*_s(τ, t) for the optimal q*, r* of (32) → A_s(t) is the optimal value of LP (13) for sink s; reason: the optimal q*, r* need not be unique (h = 0); §4.1 keeps the conventions of §3.1
--   - reading: (37), "q(t) and r(τ, t) being defined as in (34)" → (37) on the variables q, r of (32), minimized jointly with the orders; reason: (37) is "to be added to the formulation"; the reference names these variables and does not fix them at an optimum
--   - reading: "tree networks", with sources supplied by outside plants → an acyclic supplier map with one supplier per installation, several sources allowed; reason: §4.1 speaks of the sources in the plural and calls one source with one sink the special case of a series system
--   - encoding: link variables D_ki(t), link costs c_ki, K_ki and binary V_ki(t) with a big M → one order D_i(t) per installation, priced with the costs c_i, K_i of echelon i, and the fixed-cost indicator; reason: each installation has one supplier, §4.1 gives each echelon its own (c_k, K_k, h_k, p_k), and for M large enough the problems agree
--   - generalization: link capacities d_ki on the links k → i, i ∈ N(k) → a bound in ℝ ∪ {+∞} on the only supply link of each installation, plant links included; reason: +∞ on every plant link and d_ki on the others is exactly (36)
--   - generalization: the demand is always nonnegative, ŵ_k ≤ w̄_k (p. 156) → no sign condition on W̄_s or W′_{s,k}; reason: the statement holds without it, and nonnegative demand is a special case
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 159 (PDF 10), §4.2, Theorem 4.3 and Eqs. (36)–(37); p. 157 (PDF 8), formulation (32)

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkCap

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 4.3, p. 159: with link capacities (36) and echelon capacities (37), an order array is
the order part of an optimal solution of the robust network problem iff it is optimal for the
nominal network with the modified demands (34), the echelon capacities
`C'_k(t+1) = C_k - (2p_k/(p_k+h_k)) ∑_{s ∈ O(k)} A_s(t)` and the same link capacities. -/
theorem theorem_4_3 (G : Network) (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D : Fin G.N → ℕ → ℝ) :
    (∃ (Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ),
      G.IsRobustCapOptimal d Cap D Y q r) ↔
      G.IsModifiedCapOptimal d Cap D := by sorry

end RobustInventory.SingleStation.Supplement
