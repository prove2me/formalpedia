-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_TreeWidth_result_5_1_claim_3
-- name    : RobertsonSeymour1991.GM10.TreeWidth.result_5_1_claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:00:52.459981+00:00
-- url     : https://prove2.me/theorems/f62394f9-754e-4193-99e9-197fb2e5251c
-- title:
--   (5.1), proof, claim (3), p. 169 — every tree vertex has valency ≤ 3 (with claims (1), (2))
-- statement:
--   Let $G$ be a finite hypergraph with $\gamma(G) > 0$, $|E(G)| \ge 2$ and no isolated vertices. Then $G$ has a tree-decomposition $(T, \tau)$ of width $\omega(G)$ such that
--
--   1. for each $e \in E(G)$ there is a leaf $t$ of $T$ with $E(\tau(t)) = \{e\}$ and $V(\tau(t))$ the set of ends of $e$, and $E(\tau(t)) = \emptyset$ for each $t$ of valency $\ge 2$;
--   2. $|E(\tau(t))| = 1$ for each leaf $t$ of $T$;
--   3. every vertex of $T$ has valency $\le 3$.
--
--   Suppressing the vertices of valency $2$ in such a tree yields a ternary tree whose leaves are labelled bijectively by $E(G)$, i.e. a branch-decomposition, which is how the proof of (5.1) bounds $\beta(G)$ by $\omega(G) + 1$.
--
--   **Formalization Note** "We may assume" is read as the existence of such a tree-decomposition of width at most (hence exactly) $\omega(G)$; the page says the new decomposition "still satisfies (1) and (2)", so the claims are cumulative. The hypotheses are the standing assumptions of the proof (p. 168). A leaf is a vertex of valency at most $1$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 169, (5.1), proof, claim (3); standing assumptions p. 168

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_TreeWidth_TreeDecomposition

namespace RobertsonSeymour1991.GM10.TreeWidth

/-- (5.1), proof, claim (3), p. 169, cumulative with claims (1) and (2). Context of the proof
(p. 168): `γ(G) > 0`, `|E(G)| ≥ 2`, no isolated vertices. A leaf is a vertex of valency `≤ 1`
(p. 159). -/
theorem result_5_1_claim_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E)
    (hγ : 0 < G.maxEdgeSize) (hE : 2 ≤ Nat.card E) (hiso : ∀ v : V, ∃ e : E, G.inc e v) :
    ∃ (n : ℕ) (D : TreeDecomposition G n), D.WidthLE (treeWidth G) ∧
      (∀ e : E, ∃ t, (D.T.neighborSet t).ncard ≤ 1 ∧
        (D.τ t).edges = {e} ∧ (D.τ t).verts = G.ends e) ∧
      (∀ t, 2 ≤ (D.T.neighborSet t).ncard → (D.τ t).edges = ∅) ∧
      (∀ t, (D.T.neighborSet t).ncard ≤ 1 → (D.τ t).edges.ncard = 1) ∧
      (∀ t, (D.T.neighborSet t).ncard ≤ 3) := by sorry

end RobertsonSeymour1991.GM10.TreeWidth
