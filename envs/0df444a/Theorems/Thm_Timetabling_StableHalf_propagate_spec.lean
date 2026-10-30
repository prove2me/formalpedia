-- Prove2me | Theorems.Thm_Timetabling_StableHalf_propagate_spec
-- name    : Timetabling.StableHalf.propagate_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:42:10.026883+00:00
-- url     : https://prove2.me/theorems/290222d8-5dc3-4be0-8e20-4ffd78efdc81
-- title:
--   The implications of a decision are forced
-- statement:
--   Let $G$ be a graph on the nodes $x_j, \bar x_j$ ($j = 1, \dots, n$), queried through an oracle that answers its adjacency. Let $a$ be a partial assignment closed under implications, $j$ an open pair and $b \in \{\text{true}, \text{false}\}$. Run the propagation of the decision $(j, b)$ from $a$.
--
--   1. If it succeeds with $a'$, then $a'$ is closed, $a'_j = b$, $a'$ extends $a$, and every stable transversal $c$ of $G$ that extends $a$ and has $c_j = b$ also extends $a'$: the implications are forced.
--   2. If it fails, then no stable transversal of $G$ extends $a$ and has $c_j = b$.
--
--   This is the correctness of one decision of the limited backtracking: "then one considers all the implications of this choice [...] Then either we arrive to the conclusion that for some teacher no schedule can be found".
--
--   Differences from the source:
--   - generalization: the conflict graph of a CT4 instance with unit-cost adjacency → any graph on Fin n × Bool and any oracle answering its adjacency, at any tick cost and from any initial tick count; reason: correctness of propagation does not depend on the graph's origin or the oracle's cost; specializes to the conflict graph
--   - encoding: all implications of the earlier decisions have been taken into account → hypothesis IsClosed G a; reason: the invariant the page's procedure maintains between decisions
--   - encoding: the order in which implications are considered → a stack of pending nodes, each scanned against all 2n nodes; reason: the page does not fix the order; the outcome does not depend on it
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "The idea is to use a limited backtracking method which runs as follows: ...". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_IsStableTransversal
import Definitions.Def_Timetabling_StableHalf_IsClosed
import Definitions.Def_Timetabling_StableHalf_propagate

namespace Timetabling.StableHalf

/-- **The implications of a decision are forced.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"Initially one arbitrary selects a schedule for some teacher (this is a decision); then one
considers all the implications of this choice. This may fix the schedules of some other teachers.
Then either we arrive to the conclusion that for some tacher no schedule can be found. [...]"

Let `G` be a graph on `Fin n × Bool` and `adj` an oracle answering `G`'s adjacency (at any tick
cost). Let `a` be a closed partial assignment (`IsClosed G a`), `j` an open pair and `b : Bool`.
Run the propagation of the decision `(j, b)` from `a`, from any initial tick count `s₀`.

1. If it succeeds with `a'`, then `a'` is closed, `a' j = some b`, `a'` extends `a`, and every
   stable transversal `c` of `G` that extends `a` and has `c j = b` also extends `a'`.
2. If it fails, no stable transversal of `G` extends `a` and has `c j = b`. -/
theorem propagate_spec {n : ℕ} (G : SimpleGraph (Fin n × Bool)) [DecidableRel G.Adj]
    (adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool)
    (hadj : ∀ u w s, ∃ t : ℕ, (adj u w).run s = (decide (G.Adj u w), s + t))
    (a : Fin n → Option Bool) (ha : IsClosed G a) (j : Fin n) (hj : a j = none) (b : Bool)
    (s₀ : ℕ) :
    (∀ a', ((propagate adj a (j, b)).run s₀).1 = some a' →
      IsClosed G a' ∧ a' j = some b ∧ (∀ i x, a i = some x → a' i = some x) ∧
      ∀ c : Fin n → Bool, IsStableTransversal G c → (∀ i x, a i = some x → c i = x) →
        c j = b → ∀ i x, a' i = some x → c i = x) ∧
    (((propagate adj a (j, b)).run s₀).1 = none →
      ¬ ∃ c : Fin n → Bool, IsStableTransversal G c ∧ (∀ i x, a i = some x → c i = x) ∧
        c j = b) := by sorry

end Timetabling.StableHalf
