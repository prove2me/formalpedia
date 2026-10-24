-- Prove2me | Theorems.Thm_PicardFO_Fulfill_lemma_A_1
-- name    : PicardFO.Fulfill.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:47.075056+00:00
-- url     : https://prove2.me/theorems/5cead996-5ac3-421f-863a-a2bc2ade9330
-- title:
--   Lemma A.1 (corrected Q_t: capacity no longer positive) — inventories and capacities of every process dominate the sequential ones off Q_t
-- statement:
--   Let $\pi$ be a feasible FO policy satisfying Inventory Independence, Consistency and Monotonicity, and run Algorithm 1 with partition by products. For $t \ge 0$ let $Q_t$ be the set of nodes with positive initial capacity whose sequential capacity is no longer positive in one of the states $s_1, \dots, s_t$. Then in every iteration $k \ge 1$, for every process $m$, every $t$, every product $i$ and every node $j \notin Q_t$, the state of process $m$ after the first $t$ orders dominates the sequential state after the first $t$ orders:
--   $$
--   x^{k,m}_{t,i,j} \ge x^{\mathrm{seq}}_{t,i,j}, \qquad c^{k,m}_{t,j} \ge c^{\mathrm{seq}}_{t,j} \qquad (j \notin Q_t).
--   $$
--
--   The lemma is the invariant behind Theorem 3.2: away from the nodes that have run out in the sequential run, no process of any iteration is ever short of inventory or capacity relative to the sequential run.
--
--   **Formalization Note** The appendix indexes states from $x_0$ (the state after $t$ orders is $x_t$); in Lean this state is `seqState … t` and `procState … (cache … k) m t` (the latter is the paper's iteration $k + 1$, so Lean's `k ≥ 0` covers the paper's $k \ge 1$), and $Q_t$ is `Q … t`, which collects exhaustion at the states before the first $t$ orders, `seqState … 0, …, seqState … (t - 1)`. At `t = 0` the statement is trivial. Processes range over an arbitrary type, including processes that own no product.
--
--   Differences from the source:
--   - correction: Q_t = {j | τ_j ≤ t}, τ_j = min{t : c^{seq}_{t,j} = 0} → Q_t = {j : c_{1,j} > 0, c^{seq}_{u,j} ≤ 0 for some u ≤ t}; reason: over ℝ a capacity can jump past 0. Counterexample satisfying every assumption: J = 1, products A, B owned by two processes, x₁ = 3 for both at node 1, c₁ = 3/2, orders A, B, A, π = "node 1 if feasible": after 3 orders in iteration 1 process A holds 1 unit of A at node 1 and the sequential run holds 2, while the printed Q_3 is empty.
--   - reading: "x^{k,m}_{t,i,j}, ∀ j ∉ Q_t" with the appendix's indexing (x_t after t orders) → the states after t orders compared off Q_t; reason: the appendix's convention, and the stronger of the two index readings (the pre-order reading, j ∉ Q_t compared at the state before order t, also holds and follows by monotonicity of Q).
--   - generalization: t ∈ [T], processes m ∈ [M] with a partition of [I] → every t ∈ ℕ, any type of processes and any ownership map; reason: specializes to t ≤ T, ι = Fin M and a partition.
--   - encoding: iteration k ≥ 1 → `cache … k` with k ≥ 0 for the cache used in iteration k + 1; reason: Lean convention, same instances.
--   - reading: Assumption 2 with j′ arbitrary → j′ ≠ π((x, c), ω); reason: read literally only the never-fulfilling policy satisfies it, which makes the statement vacuous; the chosen reading is the weaker hypothesis.
--   - reading: Assumption 3's first clause for every decision j → for decisions j ∈ [J], second clause for every decision including 0; reason: e_{i,0} is undefined.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 12, Lemma A.1, eqs. (1)–(2)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Lemma A.1 (p. 12): in every iteration and for every process, at every node `j` not in
`Q_t`, the inventories of every product and the capacity of the process's state after the first
`t` orders are at least the sequential ones. -/
theorem lemma_A_1 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k : ℕ) (m : ι) (t : ℕ) (j : Fin J) (hj : j ∉ Q prod π s₁ ω t) :
    (∀ i, (seqState prod π s₁ ω t).x i j ≤
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).x i j) ∧
    (seqState prod π s₁ ω t).c j ≤
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) m t).c j := by sorry

end PicardFO.Fulfill
