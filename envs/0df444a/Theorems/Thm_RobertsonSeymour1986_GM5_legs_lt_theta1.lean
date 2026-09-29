-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_legs_lt_theta1
-- name    : RobertsonSeymour1986.GM5.legs_lt_theta1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:58:19.408991+00:00
-- url     : https://prove2.me/theorems/abd15509-3a4e-4363-ab56-83719de325bf
-- title:
--   (4.2) Fewer than $\theta_1$ edge-disjoint connected subgraphs with a leaf on each $A_i$
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor in which every vertex has valency at most $4$. Let $A_1,\dots,A_{\theta^2/2}$ be disjoint connected subgraphs of $G$, and let $B_1,\dots,B_n$ be pairwise edge-disjoint connected subgraphs of $G$. Suppose that for all $1\le i\le\theta^2/2$ and $1\le j\le n$ the set $V(A_i)\cap V(B_j)$ consists of a single vertex $v_{ij}$, and $v_{ij}$ has valency $1$ in $B_j$. Then
--
--   $$n<\theta_1,$$
--
--   where $\theta_1=2\alpha(\theta^2/2,\theta^2/2)$ is the parameter of Section 2. This is the upper bound that (4.6) contradicts.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.2), p. 97 (PDF p. 6); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params

namespace RobertsonSeymour1986.GM5

/-- (4.2): in a graph of maximum valency 4 without a θ-grid minor, fewer than `θ₁` pairwise
edge-disjoint connected subgraphs can each touch all of `θ²/2` disjoint connected subgraphs in a
single leaf vertex.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.2), p. 97 (PDF p. 6): "Let A₁,…, A_{θ²/2} be disjoint connected subgraphs of G ∈ 𝓕_θ, and
let B₁,…, B_n be pairwise edge-disjoint connected subgraphs of G. Suppose that for 1 ≤ i ≤ θ²/2,
1 ≤ j ≤ n there is a unique vertex v_ij in V(A_i) ∩ V(B_j), and it has valency 1 in B_j. Suppose in
addition that all vertices of G have valency ≤ 4. Then n < θ₁, where θ₁ is as defined in
Section 2."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. "A unique vertex `v_ij` in V(A_i) ∩ V(B_j)" is
`(A i).verts ∩ (B j).verts = {v}`; its valency in `B_j` is `((B j).neighborSet v).ncard`, and the
valency of a vertex in `G` is `(G.neighborSet v).ncard` (simple graph, so no loops or parallel
edges count). `θ₁` is `theta1 θ`. -/
theorem legs_lt_theta1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (A : Fin (θ ^ 2 / 2) → G.Subgraph)
    (hAc : ∀ i, (A i).Connected)
    (hAd : Pairwise (fun i i' => Disjoint (A i).verts (A i').verts))
    (n : ℕ) (B : Fin n → G.Subgraph)
    (hBc : ∀ j, (B j).Connected)
    (hBe : Pairwise (fun j j' => Disjoint (B j).edgeSet (B j').edgeSet))
    (hAB : ∀ i j, ∃ v : V, (A i).verts ∩ (B j).verts = {v} ∧ ((B j).neighborSet v).ncard = 1)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ 4) :
    n < theta1 θ := by sorry

end RobertsonSeymour1986.GM5
