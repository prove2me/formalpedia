-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_spider_or_path
-- name    : RobertsonSeymour1986.GM5.spider_or_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:00:33.428378+00:00
-- url     : https://prove2.me/theorems/ab25dc32-1eeb-4c08-ab01-709244d65d39
-- title:
--   (5.1) A spider through $p$ of the sets, or a path meeting exactly $q+1$ of them
-- statement:
--   Let $v$ be a vertex of a finite connected graph $G$, and let $p,q\ge 0$ be integers, and assume $q=0$ if $p=1$. Let $V_1,\dots,V_{p^q}\subseteq V(G)$ be disjoint and nonempty, with $v\in V_1\cup\dots\cup V_{p^q}$. Then at least one of the following holds:
--
--   1. there is a connected subgraph $C$ of $G$ with $v\in V(C)$, vertices $v_1,\dots,v_p\ne v$ of $C$, each of valency $1$ in $C$, and distinct indices $j_1,\dots,j_p\in\{1,\dots,p^q\}$ such that
--   $$V_{j_i}\cap V(C)=\{v_i\}\qquad(1\le i\le p);$$
--   2. there is a path of $G$ with initial vertex $v$ meeting exactly $q+1$ of $V_1,\dots,V_{p^q}$.
--
--   This general lemma has no excluded-minor hypothesis. The paper applies it inside each $A_i$ of a mesh in the proof of (5.2), with $p=\theta^2/2$.
--
--   **Formalization Note** The paper states the lemma for all $p,q\ge0$. The hypothesis "$p=1$ implies $q=0$" is added because the printed statement is false exactly for $p=1$, $q\ge1$. Then there is a single set $V_1$ and it contains $v$. Alternative 1 would need $v_1\ne v$ with $V_1\cap V(C)=\{v_1\}$, although $v\in V_1\cap V(C)$. Alternative 2 would need a path meeting two of one set. The paper uses only $p=\theta^2/2\ge 18$.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.1), p. 100 (PDF p. 9), with the hypothesis (p = 1 → q = 0) added (the printed lemma fails exactly for p = 1, q ≥ 1); DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- (5.1): in a connected graph, given `p^q` disjoint nonempty vertex sets one of which contains
`v`, either a connected subgraph through `v` picks out `p` of the sets in single leaves, or a path
from `v` meets exactly `q + 1` of the sets.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (5.1), p. 100 (PDF p. 9): "Let v be a vertex of a connected graph G, and let p, q ≥ 0 be
integers. Let V₁,…, V_{p^q} ⊆ V(G) be disjoint and non-empty, with v ∈ V₁ ∪ ··· ∪ V_{p^q}. Then at
least one of the following holds: (i) there is a connected subgraph C of G with v ∈ V(C), and there
are p vertices v₁,…, v_p ≠ v of C, each with valency 1 in C, and there are distinct
j₁,…, j_p ∈ {1,…, p^q}, such that V_{j_i} ∩ V(C) = {v_i} (1 ≤ i ≤ p); (ii) there is a path of G
with initial vertex v, meeting exactly q + 1 of V₁,…, V_{p^q}."

**Formalization Note** The hypothesis `p = 1 → q = 0` is added: as printed, the lemma is false
exactly when `p = 1` and `q ≥ 1` (then `p^q = 1` and `v ∈ V₁`, so (i) would need `v₁ ≠ v` with
`V₁ ∩ V(C) = {v₁}` although `v ∈ V₁ ∩ V(C)`, and (ii) would need a path meeting `q + 1 ≥ 2` of a
single set; the paper's proof divides by `p^{q−1} − 1`, which is `0` there). The paper applies (5.1)
only with `p = θ²/2 ≥ 18` (in (5.2)); the discrepancy is recorded in `HARD.md`. There is no `𝓕_θ`
hypothesis and no `θ`. `V_j` is `Vs j` (`j : Fin (p ^ q)`; Lean's `0 ^ 0 = 1` agrees with the
paper). A path with initial vertex `v` is a walk `P` from `v` with `P.IsPath`; it meets `V_j` if some
vertex of its support lies in `V_j`. The valency of `v_i` in `C` is `(C.neighborSet v_i).ncard`. -/
theorem spider_or_path {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (v : V) (p q : ℕ) (hp : p = 1 → q = 0)
    (Vs : Fin (p ^ q) → Set V) (hdisj : Pairwise (fun j j' => Disjoint (Vs j) (Vs j')))
    (hne : ∀ j, (Vs j).Nonempty) (hv : v ∈ ⋃ j, Vs j) :
    (∃ C : G.Subgraph, C.Connected ∧ v ∈ C.verts ∧
      ∃ (vs : Fin p → V) (js : Fin p → Fin (p ^ q)), Function.Injective js ∧
        (∀ i, vs i ≠ v ∧ vs i ∈ C.verts ∧ (C.neighborSet (vs i)).ncard = 1) ∧
        ∀ i, Vs (js i) ∩ C.verts = {vs i}) ∨
    (∃ (u : V) (P : G.Walk v u), P.IsPath ∧
      {j : Fin (p ^ q) | ∃ x ∈ P.support, x ∈ Vs j}.ncard = q + 1) := by sorry

end RobertsonSeymour1986.GM5
