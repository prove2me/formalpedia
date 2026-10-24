-- Prove2me | Theorems.Thm_PicardFO_Fulfill_eq_5
-- name    : PicardFO.Fulfill.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:40.658864+00:00
-- url     : https://prove2.me/theorems/10f8b963-cc7a-472f-aed9-c2d9ce8516a4
-- title:
--   Eq. (5) (corrected Q_{t_c}: capacity no longer positive) — a process's own decision is sequential, or goes to a node of Q_{t_c}, or to a node where it holds more inventory
-- statement:
--   Let $\pi$ be a feasible FO policy satisfying Inventory Independence, Consistency and Monotonicity, and run Algorithm 1 with partition by products. Fix an iteration $k \ge 1$ and an order $t$ for product $i = i(\omega_t)$, and let $m$ be the process owning $i$. Let $(x^{k,m}_t, c^{k,m}_t)$ be the state of process $m$ just before order $t$ and $(x^{\mathrm{seq}}_t, c^{\mathrm{seq}}_t)$ the sequential state just before order $t$. Then the decision $a^{k,m}_t = \pi\bigl((x^{k,m}_t, c^{k,m}_t), \omega_t\bigr)$ satisfies
--   $$
--   a^{k,m}_t \in \{a^{\mathrm{seq}}_t\} \,\cup\, Q_t \,\cup\, \{\, j \notin Q_t : x^{k,m}_{t,i,j} > x^{\mathrm{seq}}_{t,i,j} \,\},
--   $$
--   where $Q_t$ is the set of nodes with positive initial capacity whose sequential capacity is no longer positive in one of the states $s_1, \dots, s_t$ (up to and including the state before order $t$).
--
--   So even a wrong decision either goes to a node that has run out sequentially, or uses a unit of inventory that the process holds in excess of the sequential run; in both cases the inventory dominance of Lemma A.1 survives the update.
--
--   **Formalization Note** Lean order `t` is the paper's order $t_c = t + 1$; `seqState … t` and `procState … (cache … k) m t` are the states before that order (the appendix's $x_{t_c - 1}$), and the paper's $Q_{t_c}$ is `Q … (t + 1)`. `cache … k` is $\alpha^k$, so the process states are those of the paper's iteration $k + 1$; Lean's `k` ranges over all of ℕ. The statement is unconditional: no induction hypothesis is assumed.
--
--   Differences from the source:
--   - correction: Q_{t_c} = {j | τ_j ≤ t_c} with τ_j = min{t : c^{seq}_{t,j} = 0} → Q_{t_c} = {j : c_{1,j} > 0, c^{seq}_{t,j} ≤ 0 for some t ≤ t_c}; reason: over ℝ a capacity can jump from positive to negative without being 0. Counterexample satisfying every assumption: J = 1, products A, B owned by two processes, x₁ = 3 for both at node 1, c₁ = 3/2, orders A, B, A, π = "node 1 if feasible": in iteration 1 process A chooses node 1 at the third order (its capacity is 1/2), while a^{seq} = 0, the printed Q is empty, and its inventory of A at node 1 (2) equals the sequential one (2).
--   - generalization: the claim inside the induction at k = k_c, t = t_c → every iteration and every order, without the induction hypothesis; reason: the statement holds unconditionally and specializes to the induction step.
--   - generalization: processes m ∈ [M] with a partition of [I] → any type of processes and any ownership map; reason: specializes to ι = Fin M and a partition.
--   - encoding: 1-based orders, state x_{t_c−1} before order t_c → 0-based order t = t_c − 1 with the state before it, Q … (t + 1) for Q_{t_c}; reason: Lean convention, same instances.
--   - reading: Assumption 2 with j′ arbitrary → j′ ≠ π((x, c), ω); reason: read literally only the never-fulfilling policy satisfies it, which makes the statement vacuous; the chosen reading is the weaker hypothesis.
--   - reading: Assumption 3's first clause for every decision j → for decisions j ∈ [J], second clause for every decision including 0; reason: e_{i,0} is undefined.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 13, eq. (5), proof of Lemma A.1

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- Eq. (5) (p. 13): when the process `m` owning the product of order `t` evaluates `π` at
order `t` (in any iteration, with cache `cache … k`), its decision is the sequential one, or a
node of `Q_{t+1}` (exhausted in the sequential run by the state before order `t`), or a node
outside `Q_{t+1}` where the process holds strictly more inventory of that product than the
sequential run before order `t`. -/
theorem eq_5 {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι)
    (hfeas : PolicyFeasible prod π) (h1 : InvIndep prod π) (h2 : Consistent prod π)
    (h3 : MonotonePolicy prod π)
    (k t : ℕ) (m : ι) (hm : own (prod (ω t)) = m) (s : State I J)
    (hs : s = procState prod π s₁ ω own (cache prod π s₁ ω own k) m t) :
    π s (ω t) = seqAct prod π s₁ ω t ∨
      ∃ j, π s (ω t) = some j ∧
        (j ∈ Q prod π s₁ ω (t + 1) ∨
          (j ∉ Q prod π s₁ ω (t + 1) ∧
            (seqState prod π s₁ ω t).x (prod (ω t)) j < s.x (prod (ω t)) j)) := by sorry

end PicardFO.Fulfill
