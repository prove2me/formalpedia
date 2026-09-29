-- Prove2me | Theorems.Thm_ShortestConnection_Principles_necessary_condition_1
-- name    : ShortestConnection.Principles.necessary_condition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:56:25.616868+00:00
-- url     : https://prove2.me/theorems/6c3d9ed6-195c-40ed-abd0-5c1cbf821be5
-- title:
--   Necessary Condition 1 — every terminal of a SSS is directly connected to a nearest neighbor
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$ with at least two terminals, with arbitrary real edge lengths $w$, and let $F$ be a shortest spanning subtree of $G$. Then every terminal $t$ is directly connected in $F$ to at least one nearest neighbor: there is a $G$-neighbor $n$ of $t$ with
--   $$\{t,n\} \in F \quad\text{and}\quad w(\{t,n\}) \le w(\{t,m\}) \text{ for every } G\text{-neighbor } m \text{ of } t.$$
--
--   This is Prim's NC1, from which Principle 1 follows: the link P1 adds is one that some shortest network must contain. Ties between lengths are allowed, which is why the conclusion is "at least one" nearest neighbor.
--
--   **Formalization Note** The connectivity of $G$ and the existence of at least two terminals are implicit hypotheses of the paper, stated explicitly here; the second guarantees that a nearest neighbor exists. Nearest neighbors range over $G$-neighbors only (a missing edge has infinite length).
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1392, Necessary Condition 1

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Necessary Condition 1 (Prim 1957, p. 1392): every terminal in a shortest spanning subtree
`F` of the connected labelled graph `G` is directly connected to at least one nearest neighbor:
for every terminal `t` there is a `G`-neighbor `n` of `t` with `s(t, n) ∈ F` and
`w s(t, n) ≤ w s(t, m)` for every `G`-neighbor `m` of `t`. Lengths are arbitrary reals, ties are
allowed.
Implicit hypotheses made explicit: `G` is connected, and `V` has at least two terminals
(`Nontrivial V`), so that a nearest neighbor exists. -/
theorem necessary_condition_1 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : IsSSS G w F) (t : V) :
    ∃ n : V, G.Adj t n ∧ s(t, n) ∈ F ∧ ∀ m : V, G.Adj t m → w s(t, n) ≤ w s(t, m) := by sorry

end ShortestConnection.Principles
