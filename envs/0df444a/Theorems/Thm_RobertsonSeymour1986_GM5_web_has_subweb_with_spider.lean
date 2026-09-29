-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_web_has_subweb_with_spider
-- name    : RobertsonSeymour1986.GM5.web_has_subweb_with_spider
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:58:59.474604+00:00
-- url     : https://prove2.me/theorems/b1d20bda-764a-4acd-8e27-d08ee7fdf3f1
-- title:
--   (4.4) A large web contains a $(p,q)$-sub-web with a spider
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph, with at least one vertex, with no $\theta$-grid minor. Let $p,q\ge 0$ be integers and put
--
--   $$m=p\,2^{p\theta^2},\qquad n=p+q+m.$$
--
--   If $((A_1,\dots,A_m),(B_1,\dots,B_n))$ is an $(m,n)$-web in $G$, then there are $I\subseteq\{1,\dots,m\}$ and $J\subseteq\{1,\dots,n\}$ with $|I|=p$ and $|J|=q$ such that $((A_i : i\in I),(B_j : j\in J))$ is a $(p,q)$-web that has a spider.
--
--   The spider is a spider of the sub-web: it is edge-disjoint from the $B_j$ with $j\in J$ and touches each $A_i$ with $i\in I$ in a single leaf. Iterating this lemma gives (4.5).
--
--   The graph is assumed to have a vertex because a spider is a connected, hence nonempty, subgraph. With no vertices and $p=q=0$, the empty families form a $(0,0)$-web but no spider exists.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.4), p. 98 (PDF p. 7); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_WebSpiderMesh

namespace RobertsonSeymour1986.GM5

/-- (4.4): a large web in a graph without a θ-grid minor contains a `(p, q)`-sub-web with a spider.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (4.4), p. 98 (PDF p. 7): "Let G ∈ 𝓕_θ, and let p, q ≥ 0 be integers. Let m = p2^{pθ²},
n = p + q + m. Suppose that ((A₁,…, A_m), (B₁,…, B_n)) is an (m, n)-web in G. Then there exists
I ⊆ {1,…, m}, J ⊆ {1,…, n} such that |I| = p, |J| = q, and ((A_i: i ∈ I), (B_j: j ∈ J)) is a
(p, q)-web with a spider."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. `m = p · 2^{p·θ²}`. The sub-web is the pair of families
`(A_i : i ∈ I)`, `(B_j : j ∈ J)` indexed by the subsets `I`, `J`; "with a spider" means some
`C` is a spider of that sub-web (conditions for `i ∈ I`, `j ∈ J` only). `[Nonempty V]` excludes
the graph with no vertices: there, with `p = q = 0`, the empty families form a `(0, 0)`-web but a
spider (a connected, hence nonempty, subgraph) cannot exist. In every other case `p = 0` is trivial,
as the paper's proof says (a single vertex is a spider of a `(0, q)`-web), and `p > 0` forces a vertex. -/
theorem web_has_subweb_with_spider {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G)
    (p q m n : ℕ) (hm : m = p * 2 ^ (p * θ ^ 2)) (hn : n = p + q + m)
    (A : Fin m → G.Subgraph) (B : Fin n → G.Subgraph) (hW : IsWeb A B) :
    ∃ (I : Finset (Fin m)) (J : Finset (Fin n)), I.card = p ∧ J.card = q ∧
      IsWeb (fun i : I => A i) (fun j : J => B j) ∧
      ∃ C : G.Subgraph, IsSpider (fun i : I => A i) (fun j : J => B j) C := by sorry

end RobertsonSeymour1986.GM5
