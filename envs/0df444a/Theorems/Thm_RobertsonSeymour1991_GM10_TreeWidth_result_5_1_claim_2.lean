-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1_claim_2
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1_claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:00:34.892169+00:00
-- url     : https://prove2.me/theorems/8c075ead-7c96-4ef6-ac7f-ad74f0424fd8
-- title:
--   (5.1), proof, claim (2), p. 169 — every leaf part has exactly one edge (with claim (1))
-- statement:
--   Let $G$ be a finite hypergraph with $\gamma(G) > 0$, $|E(G)| \ge 2$ and no isolated vertices. Then $G$ has a tree-decomposition $(T, \tau)$ of width $\omega(G)$ that satisfies claim (1) of the proof of (5.1), namely
--
--   1. for each $e \in E(G)$ there is a leaf $t$ of $T$ with $E(\tau(t)) = \{e\}$ and $V(\tau(t))$ the set of ends of $e$, and $E(\tau(t)) = \emptyset$ for each $t$ of valency $\ge 2$,
--
--   and in addition
--
--   2. $|E(\tau(t))| = 1$ for each leaf $t$ of $T$.
--
--   After this step the leaves of $T$ correspond bijectively to the edges of $G$, as the leaves of a branch-decomposition must.
--
--   **Formalization Note** "We may assume" is read as the existence of such a tree-decomposition of width at most (hence exactly) $\omega(G)$; the page says the new decomposition "still satisfies (1)", so the claims are cumulative. The hypotheses are the standing assumptions of the proof (p. 168); the absence of isolated vertices is what lets empty leaves be deleted. A leaf is a vertex of valency at most $1$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 169, (5.1), proof, claim (2); standing assumptions p. 168

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), proof, claim (2), p. 169, cumulative with claim (1). Context of the proof (p. 168):
`γ(G) > 0`, `|E(G)| ≥ 2`, no isolated vertices. A leaf is a vertex of valency `≤ 1` (p. 159). -/
theorem result_5_1_claim_2 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (hγ : 0 < G.maxEdgeSize) (hE : 2 ≤ Nat.card E) (hiso : ∀ v : V, ∃ e : E, G.inc e v) :
    ∃ (n : ℕ) (D : TreeDecomposition G n), D.WidthLE (treeWidth G) ∧
      (∀ e : E, ∃ t, (D.T.neighborSet t).ncard ≤ 1 ∧
        (D.τ t).edges = {e} ∧ (D.τ t).verts = G.ends e) ∧
      (∀ t, 2 ≤ (D.T.neighborSet t).ncard → (D.τ t).edges = ∅) ∧
      (∀ t, (D.T.neighborSet t).ncard ≤ 1 → (D.τ t).edges.ncard = 1) := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
