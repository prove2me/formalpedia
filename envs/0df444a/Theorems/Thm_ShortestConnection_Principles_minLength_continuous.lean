-- Prove2me | Theorems.Thm_ShortestConnection_Principles_minLength_continuous
-- name    : ShortestConnection.Principles.minLength_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:57:58.22082+00:00
-- url     : https://prove2.me/theorems/ef8122d1-6e7e-4e6e-9fc0-9da442d4f7f2
-- title:
--   §III — the length L of a shortest spanning subtree is continuous in the edge lengths
-- statement:
--   Let $G$ be a connected simple graph on a finite set $V$. For edge lengths $w$ let $L(G,w)$ be the length of a shortest spanning subtree of $G$, the least of the finitely many lengths $\sum_{e\in F} w(e)$ of spanning subtrees $F$ of $G$. Then the map
--   $$w \longmapsto L(G,w)$$
--   is continuous on the space of all length assignments $w$.
--
--   Prim uses this continuity to remove the assumption of distinct lengths: perturbing the lengths slightly to break ties changes $L$ only slightly.
--
--   **Formalization Note** Lengths live in $\mathrm{Sym}^2 V \to \mathbb{R}$ with the product topology. The connectivity of $G$ is an implicit hypothesis, stated explicitly; it guarantees that spanning subtrees exist, so $L$ is a genuine minimum.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1394, §III

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §III, p. 1394: the length `L` of a shortest spanning subtree of a connected
labelled graph `G`, the smallest of the finitely many spanning subtree lengths, depends
continuously on the edge lengths `w` (product topology on `Sym2 V → ℝ`).
Implicit hypothesis made explicit: `G` is connected (so spanning subtrees exist). -/
theorem minLength_continuous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    Continuous (fun w : Sym2 V → ℝ => minLength G w) := by sorry

end ShortestConnection.Principles
