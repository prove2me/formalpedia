-- Prove2me | Theorems.Thm_PicardFO_Fulfill_sec_A_2_1_conservation
-- name    : PicardFO.Fulfill.sec_A_2_1_conservation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:30.956172+00:00
-- url     : https://prove2.me/theorems/d0a27472-9d49-4ff1-81b3-5a93a32de906
-- title:
--   §A.2.1 — capacity consumed at a node is the sum of the inventories consumed there
-- statement:
--   Consider the FO problem with initial state $s_1 = (x_1, c_1)$, an arbitrary policy $\pi$, a sequence of orders and an assignment of products to processes. Let $(x^{\mathrm{seq}}_t, c^{\mathrm{seq}}_t)$ be the states of the sequential run, and let $(x_t, c_t)$ be the states of any process of the Picard iteration simulating with any cache $\alpha$ (cached actions replayed when feasible, $a_\phi$ otherwise). Then for every time $t$ and node $j$,
--   $$
--   c_{t,j} = c_{1,j} - \sum_{i \in [I]} \bigl(x_{1,i,j} - x_{t,i,j}\bigr), \qquad c^{\mathrm{seq}}_{t,j} = c_{1,j} - \sum_{i \in [I]} \bigl(x_{1,i,j} - x^{\mathrm{seq}}_{t,i,j}\bigr).
--   $$
--
--   In words, every unit of capacity used at a node is used by fulfilling one unit of some product's inventory there. Consequently, a process holding at least the sequential inventory of every product at node $j$ also holds at least the sequential capacity at $j$, which reduces Lemma A.1's capacity inequality (2) to its inventory inequality (1).
--
--   **Formalization Note** No assumption on $\pi$ is used, and the identity holds for every cache $\alpha$, not only those produced by Algorithm 1. Times are 0-based (`procState … α m t` and `seqState … t` are the states before Lean order `t`, i.e. after $t$ orders).
--
--   Differences from the source:
--   - reading: "the capacity consumed at a node is the sum of the inventories consumed at that node. Therefore … x^{k,m} ≥ x^{seq} for all i implies c^{k,m} ≥ c^{seq}" → the identity c = c₁ − Σᵢ (x₁ − x) for process runs and for the sequential run; reason: this is the fact the sentence asserts, and the implication follows from it by monotonicity of the sum.
--   - generalization: process states of Algorithm 1's iterations → process states for an arbitrary cache α and an arbitrary policy; reason: the dynamics alone give the identity, and Algorithm 1's caches are particular α.
--   - encoding: 1-based times t ∈ [T] → 0-based times t ∈ ℕ (state after t orders); reason: Lean convention, same instances.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 12, §A.2.1 (proof of Lemma A.1, first paragraph); p. 13, capacity display before (6)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Model

namespace PicardFO.Fulfill

/-- §A.2.1 (pp. 12–13): along every run, the capacity consumed at a node equals the sum over
products of the inventory consumed there, both for every process of Algorithm 1 (any cache `α`)
and for the sequential run. No assumption on `π` is needed. -/
theorem sec_A_2_1_conservation {I J : ℕ} {Ω ι : Type*} (prod : Ω → Fin I)
    (π : State I J → Ω → Option (Fin J)) (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) :
    (∀ (α : ℕ → Option (Fin J)) (m : ι) (t : ℕ) (j : Fin J),
        (procState prod π s₁ ω own α m t).c j =
          s₁.c j - ∑ i, (s₁.x i j - (procState prod π s₁ ω own α m t).x i j)) ∧
    (∀ (t : ℕ) (j : Fin J),
        (seqState prod π s₁ ω t).c j =
          s₁.c j - ∑ i, (s₁.x i j - (seqState prod π s₁ ω t).x i j)) := by sorry

end PicardFO.Fulfill
