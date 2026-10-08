-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1_claim_1
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1_claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:00:39.014484+00:00
-- url     : https://prove2.me/theorems/c19ffca6-3a0a-4db8-b645-000631e04248
-- title:
--   (5.1), proof, claim (1), p. 169 — each edge on its own leaf (if γ>0, |E|≥2, no isolated vertices)
-- statement:
--   Let $G$ be a finite hypergraph with $\gamma(G) > 0$, $|E(G)| \ge 2$ and no isolated vertices. Then $G$ has a tree-decomposition $(T, \tau)$ of width $\omega(G)$ such that
--
--   1. for each $e \in E(G)$ there is a leaf $t$ of $T$ with $E(\tau(t)) = \{e\}$ and $V(\tau(t))$ the set of ends of $e$; and hence
--   2. $E(\tau(t)) = \emptyset$ for each $t \in V(T)$ with valency $\ge 2$.
--
--   This is the first normalization in the proof of the first inequality of (5.1): every edge is moved onto a leaf of its own, which is the shape a branch-decomposition needs.
--
--   **Formalization Note** The page's "we may assume (1)" for a tree-decomposition of width $\omega(G)$ is stated as the existence of a tree-decomposition of width at most $\omega(G)$ (hence exactly $\omega(G)$) with property (1). The hypotheses $\gamma(G) > 0$, $|E(G)| \ge 2$ and "no isolated vertex" are the standing assumptions the proof of (5.1) makes on p. 168. A leaf is a vertex of valency at most $1$ (p. 159).
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 169, (5.1), proof, claim (1); standing assumptions p. 168

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), proof, claim (1), p. 169. Context of the proof (p. 168): `γ(G) > 0`, `|E(G)| ≥ 2`, no
isolated vertices. "We may assume X" is read as: some tree-decomposition of width `ω(G)` has X.
A leaf of `T` is a vertex of valency `≤ 1` (p. 159). -/
theorem result_5_1_claim_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (hγ : 0 < G.maxEdgeSize) (hE : 2 ≤ Nat.card E) (hiso : ∀ v : V, ∃ e : E, G.inc e v) :
    ∃ (n : ℕ) (D : TreeDecomposition G n), D.WidthLE (treeWidth G) ∧
      (∀ e : E, ∃ t, (D.T.neighborSet t).ncard ≤ 1 ∧
        (D.τ t).edges = {e} ∧ (D.τ t).verts = G.ends e) ∧
      (∀ t, 2 ≤ (D.T.neighborSet t).ncard → (D.τ t).edges = ∅) := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
