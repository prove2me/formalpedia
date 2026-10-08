-- Prove2me | Theorems.Thm_ShortestConnection_Principles_necessary_condition_2
-- name    : ShortestConnection.Principles.necessary_condition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:57:03.092047+00:00
-- url     : https://prove2.me/theorems/a0ed45e3-a465-4301-86a8-d53552f5288c
-- title:
--   Necessary Condition 2 — every fragment of a SSS is linked to a nearest neighbor by a shortest available link
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$ with arbitrary real edge lengths $w$, and let $F$ be a shortest spanning subtree of $G$. Let $S \subseteq V$ be a **fragment** of $F$: a nonempty set of terminals, not all of $V$, connected by links of $F$ between members of $S$. Then there are $u \in S$ and $n \notin S$ such that $\{u,n\}$ is an edge of $G$ and a link of $F$, and
--   $$w(\{u,n\}) \le w(\{u',n'\}) \quad\text{for every edge } \{u',n'\} \text{ of } G \text{ with } u' \in S,\ n' \notin S.$$
--   That is, $S$ is connected in $F$ to a nearest neighbor $n$ by a shortest available link.
--
--   This is Prim's NC2, from which Principle 2 follows. Prim writes "path"; his proof substitutes the single link $t$–$n$, as P2 does, so the statement is read with a single link.
--
--   **Formalization Note** The connectivity of $G$, the nonemptiness of $S$ and $S \ne V$ are implicit hypotheses of the paper, stated explicitly here; the last guarantees that a nearest neighbor outside $S$ exists. The fragment hypothesis is that the subgraph of $H(F)$ induced on $S$ is connected.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1392, Necessary Condition 2

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Necessary Condition 2 (Prim 1957, p. 1392): every fragment in a shortest spanning subtree `F`
of the connected labelled graph `G` is connected to at least one nearest neighbor by a shortest
available link. A fragment of `F` is a set `S` of terminals connected by links of `F` between
members of `S`. The conclusion: some link `s(u, n) ∈ F` with `u ∈ S`, `n ∉ S` is no longer than
any edge `s(u', n')` of `G` with `u' ∈ S`, `n' ∉ S` (i.e. `n` is a nearest neighbor of `S` and
`u–n` a shortest link from `n` to `S`). The paper says "path" but its proof (p. 1393) substitutes
a single link, as P2 does.
Implicit hypotheses made explicit: `G` is connected, `S` is nonempty, and `S` is not all of `V`
(so that a nearest neighbor outside `S` exists). -/
theorem necessary_condition_2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : IsSSS G w F) (S : Finset V) (hS : S.Nonempty) (hSu : S ≠ Finset.univ)
    (hfrag : ((linkGraph F).induce (S : Set V)).Connected) :
    ∃ u ∈ S, ∃ n ∉ S, G.Adj u n ∧ s(u, n) ∈ F ∧
      ∀ u' ∈ S, ∀ n' ∉ S, G.Adj u' n' → w s(u, n) ≤ w s(u', n') := by sorry

end ShortestConnection.Principles
