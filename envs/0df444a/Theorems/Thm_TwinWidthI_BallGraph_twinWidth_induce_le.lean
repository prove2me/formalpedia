-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_twinWidth_induce_le
-- name    : TwinWidthI.BallGraph.twinWidth_induce_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:11.194193+00:00
-- url     : https://prove2.me/theorems/4bc6d73c-9f38-4806-9177-e678bbcda146
-- title:
--   §4.1, p. 3:12 — induced subgraphs do not increase twin-width
-- statement:
--   Let $G$ be a graph on a finite vertex set $V$, let $S\subseteq V$, and let $G[S]$ be the subgraph induced on $S$. For every $t\ge 0$:
--
--   1. if $\operatorname{tww}(G)\le t$ then $\operatorname{tww}(G[S])\le t$;
--   2. if the all-red trigraph $G^r=(V,\emptyset,E(G))$ has $\operatorname{tww}(G^r)\le t$, then so does $G[S]^r=(S,\emptyset,E(G[S]))$.
--
--   In other words
--   $$\operatorname{tww}(G[S])\le\operatorname{tww}(G),\qquad \operatorname{tww}(G[S]^r)\le\operatorname{tww}(G^r).$$
--
--   The paper states this for trigraphs; the two parts are the two kinds of trigraph used in this mission (graphs, and trigraphs with only red edges). It is used to pass from grids to their subgraphs.
--
--   **Formalization Note.** The induced subgraph is Mathlib's `G.induce S`, a graph on the subtype of $S$. Both parts are stated with the predicates `TwinWidthLE` and `RedTwinWidthLE` of the Setting.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:12, §4.1, "The twin-width of an induced subgraph H of a trigraph G is at most the twin-width of G"

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- §4.1, p. 3:12: the twin-width of an induced subgraph is at most the twin-width of the
(tri)graph, for graphs and for all-red trigraphs. -/
theorem twinWidth_induce_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (t : ℕ) :
    (TwinWidthI.BoolWidth.TwinWidthLE G t → TwinWidthI.BoolWidth.TwinWidthLE (G.induce (S : Set V)) t) ∧
    (RedTwinWidthLE G t → RedTwinWidthLE (G.induce (S : Set V)) t) := by sorry

end TwinWidthI.BallGraph
