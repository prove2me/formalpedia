-- Prove2me | Theorems.Thm_PicardFO_Fulfill_lemma_A_1_skip_step
-- name    : PicardFO.Fulfill.lemma_A_1_skip_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:35.097806+00:00
-- url     : https://prove2.me/theorems/192e4608-09c4-467b-9a78-f04ee3b35507
-- title:
--   Proof of Lemma A.1, skip step (corrected: = → ≥) — a non-owner process holds at least the owner's previous-iteration inventory
-- statement:
--   Consider the FO problem with an arbitrary policy $\pi$, initial state $s_1 = (x_1, c_1)$, a sequence of orders, and Algorithm 1 with partition by products. Let $i$ be a product owned by process $m'$, and let $m \ne m'$ be any other process. Write $x^{k,m}_{t}$ for the inventory of process $m$ after $t$ orders in iteration $k$ of Algorithm 1. Then:
--
--   1. in iteration $1$ (cache $\alpha^0 \equiv a_\phi$), process $m$ consumes no inventory of product $i$: $x^{1,m}_{t,i,j} = x_{1,i,j}$ for all $t$ and $j$;
--   2. in every iteration $k \ge 2$, process $m$ holds at least as much inventory of product $i$ as its owner held in the previous iteration:
--   $$
--   x^{k,m}_{t,i,j} \;\ge\; x^{k-1,m'}_{t,i,j} \qquad \text{for all } t \text{ and all nodes } j.
--   $$
--
--   Process $m$ never evaluates $\pi$ on orders of product $i$; it replays the actions that $m'$ took on them in the previous iteration, but only when they are feasible in its own state. This is the case of the induction for Lemma A.1 in which the product of the current order belongs to another process.
--
--   **Formalization Note** Lean's `procState … (cache … k) m t` is process `m` after `t` orders in the paper's iteration $k + 1$; item 2 is stated for all Lean `k ≥ 0`, i.e. the paper's iterations $k \ge 2$, and item 1 is the paper's iteration $1$ (the paper's "iteration $0$" with no order fulfilled). No assumption on $\pi$ is used. `m` ranges over all processes other than the owner, including processes that own no product.
--
--   Differences from the source:
--   - correction: a^{k,m}_t = a^{k−1,m′}_t for every order of i_c and x^{k,m}_{t,i_c,j} = x^{k−1,m′}_{t,i_c,j} → x^{k,m}_{t,i,j} ≥ x^{k−1,m′}_{t,i,j}; reason: Algorithm 1, line 7, replaces an infeasible cached action by a_φ. Counterexample satisfying every assumption: J = 1, c₁ = 1, products A (process 1) and B (process 2) with ample inventory, orders B then A, π = "fulfil at node 1 when feasible". In iteration 2 process 2 has capacity 0 at A's order, so it does not replay α¹ = 1 there: x^{2,2}_{2,A,1} = x_{1,A,1} > x^{1,1}_{2,A,1} = x_{1,A,1} − 1.
--   - reading: iteration k − 1 = 0 in the paper's induction ("all orders are not fulfilled") → item 1, process states of iteration 1 equal the initial inventory of i; reason: the paper's base case convention.
--   - generalization: processes m ∈ [M] with a partition of [I] → any type of processes and any ownership map, m any process other than the owner; reason: specializes to M processes and a partition.
--   - encoding: 1-based times and iterations → 0-based times, `cache … k` for α^k; reason: Lean convention, same instances.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 12, §A.2.1, proof of Lemma A.1 (case i_c handled by a process m′ ≠ m)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Proof of Lemma A.1, skip step (p. 12), corrected (`=` → `≥`): a process `m` that does
not own product `i` holds, at every time, at least as much inventory of `i` at every node as
the owner of `i` held in the previous iteration; in the first iteration (cache `α⁰ ≡ aϕ`) it
has not consumed any inventory of `i`. No assumption on `π` is needed. -/
theorem lemma_A_1_skip_step {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (m : ι) (i : Fin I) (hm : own i ≠ m) :
    (∀ (t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own (cache prod π s₁ ω own 0) m t).x i j = s₁.x i j) ∧
    (∀ (k t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own (cache prod π s₁ ω own k) (own i) t).x i j ≤
          (procState prod π s₁ ω own (cache prod π s₁ ω own (k + 1)) m t).x i j) := by sorry

end PicardFO.Fulfill
