-- Prove2me | Theorems.Thm_PerishShip_Waste_sofFull_pathwise_regret
-- name    : PerishShip.Waste.sofFull_pathwise_regret
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T21:12:45.369683+00:00
-- url     : https://prove2.me/theorems/9cf2007c-35e0-4d37-b7fb-492794db549a
-- title:
--   SOF in full has bounded sample-path regret in warehouse waste
-- statement:
--   Work in the two-echelon model of Akkaş–Honhon (§4.1): a product with shelf life $N\ge1$, warehouse order-up-to level $S^W$, store capacity $L$, and a fraction $\gamma\in[0,1]$ of FIFO shoppers. A state $s=(x,y)$ records the warehouse and store stock by age; the warehouse is replenished to $S^W$, a shipment $q$ is feasible if $q_i\le \bar x_i$ for each age $i$ and $\sum_i q_i+\sum_i y_i\le L$, and the warehouse waste of the period is $W^W(s,q)=\bar x_{N-1}-q_{N-1}$, the unshipped part of the oldest cohort. Let $\mathrm{SOF}(s)$ be the shipment that ships oldest first and in full, i.e. the largest feasible total quantity $\min(L-\sum_i y_i,\,S^W)$ taken from the oldest cohorts first.
--
--   **Claim.** There is a constant $C$, depending only on the parameters, such that for every sequence of shopper populations $\lambda_0,\lambda_1,\dots$, every pair of feasible initial states $u_0$ and $v_0$, and every sequence of shipments $a_t$ that is feasible along the trajectory $v_{t+1}=\mathrm{next}(v_t,a_t,\lambda_t)$, the trajectory $u_{t+1}=\mathrm{next}(u_t,\mathrm{SOF}(u_t),\lambda_t)$ satisfies, for every horizon $T$,
--   $$\sum_{t<T} W^W\big(u_t,\mathrm{SOF}(u_t)\big)\ \le\ \sum_{t<T} W^W(v_t,a_t)+C.$$
--
--   In words: along any realisation of demand, the cumulative warehouse waste of shipping oldest first in full exceeds that of any feasible shipping sequence — even one that knows the future demand and starts from a different feasible state — by at most a bounded amount. Shipping in full is not optimal over a finite horizon (filling the store with fresh stock can block later shipments of old stock), so a constant $C$ is needed; the claim is the sample-path content behind the first sentence of Theorem 1 (p. 15). Combined with the general block argument `PerishShip.Waste.avg_optimal_of_pathwise_regret` it yields that SOF in full minimizes the long-run average warehouse waste.
--
--   **Formalization Note** States, dynamics (`next`), feasibility and the shipment `sofFull` are those of `Def_PerishShip_Waste_Model`; trajectories are arbitrary functions satisfying the recursions. Exhaustive computation on small instances ($N\le5$, $S^W\le4$, $L\le3$, several $\gamma$) confirms that the worst-case regret is finite.
-- source:
--   Sample-path content of Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), Theorem 1 (first sentence: SOF shipping in full minimizes long-run average warehouse waste)

import Mathlib
import Definitions.Def_PerishShip_Waste_Model

namespace PerishShip.Waste

/-- Sample-path regret bound for shipping oldest first in full (warehouse waste). -/
theorem sofFull_pathwise_regret (P : Params) (hP : P.Standing) :
    ∃ C : ℕ, ∀ (lam : ℕ → ℕ) (u v : ℕ → State P) (a : ℕ → Vec P),
      (u 0).Feasible → (v 0).Feasible →
      (∀ t, u (t + 1) = next (u t) (sofFull (u t)) (lam t)) →
      (∀ t, ShipFeasible (v t) (a t)) →
      (∀ t, v (t + 1) = next (v t) (a t) (lam t)) →
      ∀ T, ∑ t ∈ Finset.range T, ww hP.1 (u t) (sofFull (u t)) ≤
        ∑ t ∈ Finset.range T, ww hP.1 (v t) (a t) + C := by sorry

end PerishShip.Waste
