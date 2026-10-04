-- Prove2me | Theorems.Thm_ShortestConnection_Principles_distinct_lengths_links_in_every_sss
-- name    : ShortestConnection.Principles.distinct_lengths_links_in_every_sss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:57:28.569831+00:00
-- url     : https://prove2.me/theorems/474f555f-8bc5-46fe-b0a3-80393f233e52
-- title:
--   §III — with distinct lengths, every link permitted by P1 or P2 lies in every SSS
-- statement:
--   Let $G$ be a simple graph on a finite set $V$ whose edge lengths are pairwise distinct:
--   $$e, f \in E(G),\ w(e) = w(f) \implies e = f.$$
--   Let $e_0,\dots,e_{k-1}$ be any construction by P1 and P2 and let $F$ be any shortest spanning subtree of $G$. Then every link $e_i$ of the construction belongs to $F$.
--
--   This is the first half of Prim's validation of the construction principles, under his temporary assumption that all distances are different: P1 and P2 only permit the addition of links which NC1 and NC2 show must appear in the final shortest network.
--
--   **Formalization Note** "All distances between terminals are different" becomes injectivity of $w$ on the edges of $G$; lengths of non-edges are unconstrained.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), pp. 1392-1393, §III (the temporary assumption of distinct distances, and 'From NC1 follows P1 … From the validity of NC2 follows P2')

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §III, p. 1393 ("From NC1 follows P1, which merely permits the addition of links
which NC1 shows have to appear in the final SCN. … the links whose addition is permitted by P2
are all necessary, by NC2, in the final SCN"), under the temporary assumption of pp. 1392–1393
that all distances are different: if the edge lengths of `G` are pairwise distinct, then every
link of every construction by P1 and P2 belongs to every shortest spanning subtree of `G`. -/
theorem distinct_lengths_links_in_every_sss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → w e = w f → e = f)
    (l : List (Sym2 V)) (hl : IsConstruction G w l) (F : Finset (Sym2 V)) (hF : IsSSS G w F) :
    ∀ e ∈ l, e ∈ F := by sorry

end ShortestConnection.Principles
