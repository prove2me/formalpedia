-- Prove2me | Theorems.Thm_PicardFO_Fulfill_eq_3
-- name    : PicardFO.Fulfill.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:43.577349+00:00
-- url     : https://prove2.me/theorems/1a6ba676-c5f9-4c76-86ce-6bdbe1ee773a
-- title:
--   Eq. (3) (corrected: t ≤ τ̃_k → t < τ̃_k) — the cache of iteration k is correct at every order with fewer than k exhausted nodes
-- statement:
--   Let $\pi$ be a feasible FO policy satisfying Inventory Independence, Consistency and Monotonicity, and run Algorithm 1 with partition by products. For an order $t \ge 1$ let $Q_t$ be the set of nodes with positive initial capacity whose sequential capacity is no longer positive in one of the states $s_1, \dots, s_t$ (up to and including the state before order $t$). Then for every iteration $k \ge 1$ and every order $t$,
--   $$
--   |Q_t| < k \;\Longrightarrow\; \alpha^k_t = a^{\mathrm{seq}}_t .
--   $$
--   Equivalently, with $\tilde\tau_1 \le \tilde\tau_2 \le \cdots$ the sorted exhaustion times, $\alpha^k_t = a^{\mathrm{seq}}_t$ for all $t < \tilde\tau_k$.
--
--   Each iteration of Algorithm 1 thus extends the correct prefix of the cache at least past the next time a node runs out in the sequential run; Theorem 3.2 is the case $t \le T$, $k \ge |Q_T| + 1$.
--
--   **Formalization Note** Lean order `t` is the paper's order $t + 1$, so the paper's $Q_{t+1}$ is `Q … (t + 1)`. `cache … k` is $\alpha^k$; for `k = 0` the hypothesis is never met. Orders range over all of ℕ (no horizon).
--
--   Differences from the source:
--   - correction: 1 ≤ t ≤ τ̃_k → t < τ̃_k, written |Q_t| < k; reason: at t = τ̃_k the printed claim fails. Counterexample satisfying every assumption: J = 1, products A, B owned by two processes, ample inventory, c₁ = 1, orders A then B, π = "node 1 if feasible": τ₁ = 2, a^{seq} = (1, 0), but α¹ = (1, 1) since B's owner does not see A's order; §3.1 (p. 5) states the strict form.
--   - correction: τ_j = min{t : c^{seq}_{t,j} = 0} → exhaustion as c^{seq}_{t,j} ≤ 0 at a node with c_{1,j} > 0; reason: over ℝ a capacity can jump past 0 (counterexample: J = 1, c₁ = 3/2, orders A, B, A, π = fulfil if feasible; no τ_j ≤ 3 printed, yet α¹_3 = 1 ≠ a^{seq}_3 = 0).
--   - generalization: t ∈ [T], processes m ∈ [M] with a partition of [I] → every order t ∈ ℕ, any type of processes and any ownership map; reason: specializes to t ≤ T, ι = Fin M and a partition.
--   - encoding: 1-based orders → 0-based orders, Q … (t + 1) for Q_{t+1}; reason: Lean convention, same instances.
--   - reading: Assumption 2 with j′ arbitrary → j′ ≠ π((x, c), ω); reason: read literally only the never-fulfilling policy satisfies it, which makes the statement vacuous; the chosen reading is the weaker hypothesis.
--   - reading: Assumption 3's first clause for every decision j → for decisions j ∈ [J], second clause for every decision including 0; reason: e_{i,0} is undefined.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 12, eq. (3), proof of Theorem 3.2 (strict form also in §3.1, p. 5)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Eq. (3) (p. 12), corrected (`t ≤ τ̃_k` → `t < τ̃_k`): in iteration `k`, the cached action of
order `t` is the sequential one whenever fewer than `k` nodes are in `Q_{t+1}`. -/
theorem eq_3 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k t : ℕ) (h : (Q prod π s₁ ω (t + 1)).card < k) :
    cache prod π s₁ ω own k t = seqAct prod π s₁ ω t := by sorry

end PicardFO.Fulfill
