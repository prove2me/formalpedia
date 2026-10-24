-- Prove2me | Theorems.Thm_PicardFO_Fulfill_theorem_3_2
-- name    : PicardFO.Fulfill.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:54.430082+00:00
-- url     : https://prove2.me/theorems/b4675b1d-640f-426e-8918-73afbc469e03
-- title:
--   Theorem 3.2 (corrected: a node runs out when its capacity is no longer positive) — Picard iteration for fulfillment converges in at most |Q_T| + 1 iterations
-- statement:
--   Consider the fulfillment optimization problem with $I$ products, $J$ nodes, real initial inventories $x_1 \in \mathbb R^{I \times J}$ and capacities $c_1 \in \mathbb R^{J}$, a sequence of orders $\omega_1, \omega_2, \dots$ for products $i(\omega_t)$, and a feasible policy $\pi$ satisfying Inventory Independence, Consistency and Monotonicity (Assumptions 1–3). Run Algorithm 1 (the Picard iteration) with the time steps partitioned by products: each product is owned by one process, and order $t$ is handled by the owner of $i(\omega_t)$. Let $a^{\mathrm{seq}}_t$ be the actions of the sequential run and $\alpha^k_t$ the cache after iteration $k$. Fix a horizon $T$ and let
--   $$
--   Q_T = \{\, j \in [J] : c_{1,j} > 0 \text{ and } c^{\mathrm{seq}}_{t,j} \le 0 \text{ for some } t \in [T] \,\}
--   $$
--   be the set of nodes that run out of capacity in the sequential run. Then:
--
--   1. for every iteration $k \ge |Q_T| + 1$,
--   $$
--   \alpha^k_t = a^{\mathrm{seq}}_t \qquad \text{for all } t \in [T];
--   $$
--   2. whenever the convergence test of Algorithm 1 succeeds at an iteration $k \ge 1$, that is $\alpha^k_t = \alpha^{k-1}_t$ for all $t \in [T]$, the returned cache is the sequential action sequence: $\alpha^k_t = a^{\mathrm{seq}}_t$ for all $t \in [T]$.
--
--   The number of Picard iterations needed is thus bounded by one more than the number of nodes that run out of capacity, independently of the horizon $T$ and of the number of products and processes. Since each iteration evaluates the policy on $\max_m |T_m|$ orders per process in parallel, this bound is what turns the Picard iteration into a speed-up of policy simulation for fulfillment.
--
--   **Formalization Note** Actions are `Option (Fin J)` (`none` is the paper's action $0 = a_\phi$); orders are 0-based (Lean order `t < T` is the paper's order $t + 1 \in [T]$); `Q … T` is the paper's $Q_T$ computed over the sequential states $s_1, \dots, s_T$ (the state after the last order is not included); `cache … k` is $\alpha^k$; processes are an arbitrary type `ι` with ownership map `own`. Runs are defined for all orders, and the horizon enters only through `Q … T` and `t < T`; no step of Algorithm 1 at order $t$ depends on later orders.
--
--   Differences from the source:
--   - correction: 𝒬_T = |{j : τ_j ≤ T}| with τ_j = min{t : c^{seq}_{t,j} = 0} → |{j : c_{1,j} > 0, c^{seq}_{t,j} ≤ 0 for some t ∈ [T]}|; reason: as printed the theorem is false over the paper's real capacities. Counterexample satisfying every assumption: J = 1, products A, B owned by two processes, x₁ = 3 for both at node 1, c₁ = 3/2, orders A, B, A, π = "node 1 if feasible, else 0": sequential capacities 3/2, 1/2, −1/2 are never 0, so 𝒬_T = 0, but a^{seq} = (1, 1, 0) and α¹ = (1, 1, 1). On integer data the corrected Q_T is contained in the printed one, so the corrected statement implies the printed one there.
--   - reading: Assumption 2 with j′ arbitrary → j′ ≠ π((x, c), ω); reason: read literally only the never-fulfilling policy satisfies it (a policy choosing j would have to keep choosing j after c_j is set to 0), which makes the theorem vacuous; the chosen reading is the weaker hypothesis.
--   - reading: Assumption 3's first clause for every decision j → for decisions j ∈ [J]; second clause for every decision including 0; reason: e_{i,0} is undefined.
--   - reading: "converges in at most 𝒬_T + 1 iterations" → the cache equals a^{seq} on [T] in every iteration k ≥ |Q_T| + 1, and the cache returned by the convergence test is a^{seq}; reason: the sense used in the paper (proof of Proposition 2.1, p. 12, "setting k = T"); the test of line 10 needs one more iteration to observe convergence.
--   - generalization: M processes and a partition of [I] → any type of processes and any ownership map (processes may own no product); reason: specializes to ι = Fin M and a partition.
--   - encoding: action set {0} ∪ [J], 1-based orders, finite disturbance sequence {ω_t : t ∈ [T]} → Option (Fin J), 0-based orders, ω : ℕ → Ω with t < T; reason: Lean convention, same instances (later orders never influence earlier steps).
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 6, Theorem 3.2 (with §3.1, p. 5, for τ_j and Q_t; proof in App. A.2, pp. 12–13)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Theorem 3.2 (p. 6), corrected (a node runs out when its capacity is no longer positive):
for a feasible policy satisfying Assumptions 1–3, the cache of Algorithm 1 (partition by
products) equals the sequential actions on the first `T` orders in every iteration
`k ≥ |Q_T| + 1`; and whenever the convergence test of line 10 succeeds at an iteration
`k ≥ 1`, the returned cache is the sequential one. -/
theorem theorem_3_2 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π) (T : ℕ) :
    (∀ k : ℕ, (Q prod π s₁ ω T).card + 1 ≤ k →
        ∀ t < T, cache prod π s₁ ω own k t = seqAct prod π s₁ ω t) ∧
    (∀ k : ℕ, 1 ≤ k →
        (∀ t < T, cache prod π s₁ ω own k t = cache prod π s₁ ω own (k - 1) t) →
        ∀ t < T, cache prod π s₁ ω own k t = seqAct prod π s₁ ω t) := by sorry

end PicardFO.Fulfill
