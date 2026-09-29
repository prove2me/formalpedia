-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_linkage_or_hitting_set
-- name    : RobertsonSeymour1986.GM5.linkage_or_hitting_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:57:01.610599+00:00
-- url     : https://prove2.me/theorems/f7fb545b-b6ca-403d-8d67-7d7c18201a88
-- title:
--   (3.2) Many disjoint connected subgraphs meeting all $V_i$, or a small hitting set
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Let $V_1,\dots,V_k\subseteq V(G)$ with $k\ge 2$, and let $n\ge 0$. Then at least one of the following holds:
--
--   1. there are disjoint connected subgraphs $B_1,\dots,B_n$ of $G$ such that each $B_j$ meets each $V_i$;
--   2. there is a set $X\subseteq V(G)$ with
--   $$|X|<\alpha(k,n)$$
--   such that every connected subgraph of $G$ meeting all of $V_1,\dots,V_k$ also meets $X$.
--
--   Here $\alpha(k,n)$ is the parameter of Section 2 of the paper, which depends on $\theta$. The statement is an approximate min–max relation, and it fails without the excluded-grid hypothesis.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (3.2), p. 96 (PDF p. 5); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params

namespace RobertsonSeymour1986.GM5

/-- (3.2): in a graph without a θ-grid minor, either there are `n` disjoint connected subgraphs
each meeting all of `V₁, …, V_k`, or fewer than `α(k, n)` vertices meet every connected subgraph
that meets all of `V₁, …, V_k`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (3.2), p. 96 (PDF p. 5): "Let G ∈ 𝓕_θ, and let V₁,…, V_k ⊆ V(G), where k ≥ 2. Let n ≥ 0 be an
integer. Then at least one of the following is true: (i) there are disjoint connected subgraphs
B₁,…, B_n of G such that each B_j meets each V_i (1 ≤ i ≤ k, 1 ≤ j ≤ n) (ii) there exists
X ⊆ V(G) with |X| < α(k, n) such that every connected subgraph of G which meets all of V₁,…, V_k
also meets X."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. `G` is a finite simple graph. `V_i` is `Vs i`
(`i : Fin k`), `B_j` is `B j` (`j : Fin n`); "connected subgraph" is `Subgraph.Connected`
(which includes nonemptiness). `α` is `alpha θ`. -/
theorem linkage_or_hitting_set {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (k : ℕ) (hk : 2 ≤ k) (Vs : Fin k → Set V) (n : ℕ) :
    (∃ B : Fin n → G.Subgraph, (∀ j, (B j).Connected) ∧
        Pairwise (fun j j' => Disjoint (B j).verts (B j').verts) ∧
        ∀ i j, ((B j).verts ∩ Vs i).Nonempty) ∨
    (∃ X : Finset V, X.card < alpha θ k n ∧
        ∀ C : G.Subgraph, C.Connected → (∀ i, (C.verts ∩ Vs i).Nonempty) →
          (C.verts ∩ (X : Set V)).Nonempty) := by sorry

end RobertsonSeymour1986.GM5
