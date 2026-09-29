-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_two_heavy_or_central_vertex
-- name    : RobertsonSeymour1986.GM5.two_heavy_or_central_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:02:27.409417+00:00
-- url     : https://prove2.me/theorems/78b3a0ba-856e-4e7a-8fca-12ba374333f1
-- title:
--   (6.2) Two disjoint heavy connected sets, or a vertex leaving only light components
-- statement:
--   Let $G$ be a finite connected graph, let $w:V(G)\to\mathbb Z_{\ge0}$, and write $w(X)=\sum_{v\in X}w(v)$ for $X\subseteq V(G)$. Let $k>0$ be an integer with
--
--   $$k\le \frac{w(V(G))+2}{3}.$$
--
--   Then **exactly one** of the following holds:
--
--   1. there are disjoint subsets $V_1,V_2$ of $V(G)$ such that $G|V_1$ and $G|V_2$ are both connected and $w(V_1),w(V_2)\ge k$;
--   2. there is a vertex $v$ of $G$ such that $w(V(C))<k$ for every component $C$ of $G\setminus v$.
--
--   Here $G|X$ is the subgraph induced on $X$. The lemma is proved from Tutte's ear-type ordering of 2-connected graphs and is the tool behind (6.3).
--
--   **Formalization Note** The condition on $k$ is stated as $3k\le w(V(G))+2$, which is equivalent.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.2), p. 103 (PDF p. 12), with the weight notation of p. 103; DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- (6.2): in a connected vertex-weighted graph, exactly one of: two disjoint connected vertex sets
of weight `≥ k`, or a vertex whose removal leaves only components of weight `< k`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.2), p. 103 (PDF p. 12). Preamble (p. 103): "Let Z⁺ denote the set of non-negative
integers. If G is a graph and w: V(G) → Z⁺ is a function and X ⊆ V(G), then w(X) denotes
Σ_{v∈X} w(v)." Statement: "Let G be a connected graph, let w: V(G) → Z⁺ be some function, and let
k > 0 be an integer with k ≤ (w(V(G)) + 2)/3. Then exactly one of the following is true: (i) there
are disjoint subsets V₁, V₂ of V(G) such that G|V₁, G|V₂ are both connected and w(V₁), w(V₂) ≥ k;
(ii) there is a vertex v of G such that w(V(C)) < k for every component C of G\v."

**Formalization Note** No `θ`. "Exactly one" is `Xor` (exclusive or). The rational condition
`k ≤ (w(V(G)) + 2)/3` is the equivalent `3k ≤ w(V(G)) + 2` in `ℕ`. `w(X)` is the finite sum
`∑ᶠ x ∈ X, w x`; `G|V_i` is `G.induce V_i`; a component `C` of `G\v` is a connected component of
`G.induce {v}ᶜ`, with vertex set `Subtype.val '' C.supp`. -/
theorem two_heavy_or_central_vertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (w : V → ℕ) (k : ℕ) (hk : 0 < k) (hkw : 3 * k ≤ (∑ x, w x) + 2) :
    Xor
      (∃ V₁ V₂ : Set V, Disjoint V₁ V₂ ∧ (G.induce V₁).Connected ∧ (G.induce V₂).Connected ∧
        k ≤ ∑ᶠ x ∈ V₁, w x ∧ k ≤ ∑ᶠ x ∈ V₂, w x)
      (∃ v : V, ∀ C : (G.induce ({v}ᶜ : Set V)).ConnectedComponent,
        ∑ᶠ x ∈ Subtype.val '' C.supp, w x < k) := by sorry

end RobertsonSeymour1986.GM5
