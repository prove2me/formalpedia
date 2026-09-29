-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_adjacent_families_small
-- name    : RobertsonSeymour1986.GM5.adjacent_families_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:57:43.290403+00:00
-- url     : https://prove2.me/theorems/8c25944b-8860-466b-a06f-9e84da08d6e9
-- title:
--   (4.1) Two mutually adjacent families of disjoint connected subgraphs cannot both be large
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Let $A_1,\dots,A_m,B_1,\dots,B_n$ be pairwise disjoint connected subgraphs of $G$ such that for all $i,j$ some vertex of $A_i$ is adjacent in $G$ to some vertex of $B_j$. Then
--
--   $$m<\theta^2/2 \quad\text{or}\quad n<\theta^2/2.$$
--
--   Contracting the $A_i$ and $B_j$ gives a $K_{m,n}$, and $K_{\theta^2/2,\theta^2/2}$ contains the $\theta$-grid. The lemma is used in the proofs of (4.2) and (5.2).
--
--   **Formalization Note** Disjointness covers all $m+n$ subgraphs: the $A_i$ among themselves, the $B_j$ among themselves, and each $A_i$ with each $B_j$.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.1), p. 97 (PDF p. 6); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor

namespace RobertsonSeymour1986.GM5

/-- (4.1): two families of disjoint connected subgraphs, pairwise joined by edges, cannot both have
`θ²/2` members in a graph without a θ-grid minor.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.1), p. 97 (PDF p. 6): "Let G ∈ 𝓕_θ. Let A₁,…, A_m, B₁,…, B_n be disjoint connected
subgraphs of G such that for 1 ≤ i ≤ m, 1 ≤ j ≤ n there is a vertex of A_i and a vertex of B_j which
are adjacent in G. Then either m < θ²/2 or n < θ²/2."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. "Disjoint" ranges over all `m + n` subgraphs: the `A_i` among
themselves, the `B_j` among themselves, and every `A_i` with every `B_j` (vertex-disjointness).
`θ ^ 2 / 2` is exact since `θ` is even. -/
theorem adjacent_families_small {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (m n : ℕ) (A : Fin m → G.Subgraph) (B : Fin n → G.Subgraph)
    (hAc : ∀ i, (A i).Connected) (hBc : ∀ j, (B j).Connected)
    (hAd : Pairwise (fun i i' => Disjoint (A i).verts (A i').verts))
    (hBd : Pairwise (fun j j' => Disjoint (B j).verts (B j').verts))
    (hABd : ∀ i j, Disjoint (A i).verts (B j).verts)
    (hadj : ∀ i j, ∃ x ∈ (A i).verts, ∃ y ∈ (B j).verts, G.Adj x y) :
    m < θ ^ 2 / 2 ∨ n < θ ^ 2 / 2 := by sorry

end RobertsonSeymour1986.GM5
