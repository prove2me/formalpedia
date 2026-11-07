-- Prove2me | Theorems.Thm_PredAdvice_lemma_4_2
-- name    : PredAdvice.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:19.126593+00:00
-- url     : https://prove2.me/theorems/5c54cdf2-bee1-4a0f-8326-d68915639849
-- title:
--   Lemma 4.2 — shared trees $T^{out}_h$, $T^{in}_h$ for separated small pairs
-- statement:
--   Let $2\le D\le|V|$, $L\ge1$, $\chi$ be colourings, and let $F^{out}_u,F^{in}_v$ satisfy properties 1–3 of Lemma 4.1, with $h\ne u$ and $h$ reachable from $u$ whenever $h\in F^{out}_u$, and $h\ne v$ and $v$ reachable from $h$ whenever $h\in F^{in}_v$. Put $f=\sum_u|F^{out}_u|+\sum_v|F^{in}_v|$. For every $h$ there are shortest-path trees $T^{out}_h$ (directed toward $h$) and $T^{in}_h$ (directed away from $h$), rooted at $h$, with
--   $$
--   V(T^{out}_h)=\{h\}\cup\{u : h\in F^{out}_u\},\qquad V(T^{in}_h)=\{h\}\cup\{v : h\in F^{in}_v\},
--   $$
--   $\sum_h(|E(T^{out}_h)|+|E(T^{in}_h)|)=f$, and for every separated small pair $(u,v)$ with $u\ne v$ there are $x,y$ with $x=y$ or $(x,y)\in E$, $u\in V(T^{out}_x)$, $v\in V(T^{in}_y)$ and $\mathrm{dist}(u,x)+\mathbf 1_{x\ne y}+\mathrm{dist}(y,v)=\mathrm{dist}(u,v)$: the $u$–$x$ path in $T^{out}_x$, the edge $(x,y)$ when $x\ne y$, and the $y$–$v$ path in $T^{in}_y$ form a shortest $u$–$v$ path.
--
--   The trees are shared by all separated small pairs, and their total size is the hop count $f$ of Lemma 3.5.
--
--   Differences from the source:
--   - generalization: the subfamilies supplied by Lemma 4.1 for the §3.3 sets → any families with properties 1–3 whose members are proper reachable vertices; reason: the proof uses only these facts; for the paper's families every h ∈ F^out_u lies in some H°_{u,b}, so they hold
--   - encoding: a shortest u–v path made of two tree paths and an edge → u ∈ V(T^out_x), v ∈ V(T^in_y) and the exact-length identity; reason: tree paths in shortest-path trees are shortest paths of length dist
--   - generalization: separation with respect to the colourings χ fixed in Lemma 3.3 → separation with respect to any colourings χ : Fin L → V → Fin (2D); reason: the proof uses no property of the specific colourings; the paper's χ is one instance
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 4.2, p.20

import Mathlib
import Definitions.Def_PredAdvice_IsSeparated
import Definitions.Def_PredAdvice_RootedTree

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 4.2** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §4.1, p.20). Let `F^out_u, F^in_v` be families with the three properties of
Lemma 4.1, whose members are proper reachable vertices (`h ∈ F^out_u ⇒ h ≠ u` and `h` reachable from
`u`; `h ∈ F^in_v ⇒ h ≠ v` and `v` reachable from `h`), and `f := ∑_u |F^out_u| + ∑_v |F^in_v|`.
For every `h ∈ V` there are shortest-path trees `T^out_h`, `T^in_h` rooted at `h`, directed toward
and away from `h`, with `V(T^out_h) = {h} ∪ {u | h ∈ F^out_u}` and `V(T^in_h) = {h} ∪ {v | h ∈ F^in_v}`,
such that `∑_h (|E(T^out_h)| + |E(T^in_h)|) = f`, and for every nontrivial separated small pair
`(u, v)` there are `x, y` with `x = y` or `(x, y) ∈ E` such that the `u–x` path in `T^out_x`, then
`(x, y)` when `x ≠ y`, then the `y–v` path in `T^in_y` is a shortest `u–v` path.

**Formalization Note** The paper's families are the subsets of Lemma 4.1 of the §3.3 sets; each
member `h ∈ F^out_u` there lies in `H°_{u,b}` for some `b`, so the membership hypotheses hold; the
statement assumes only these and the three properties. A tree path in a shortest-path tree has
length equal to the distance, so "the concatenation is a shortest path" is `u ∈ V(T^out_x)`,
`v ∈ V(T^in_y)` and `dist(u, x) + 1_{x≠y} + dist(y, v) = dist(u, v)`. -/
theorem lemma_4_2 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ)
      (χ : Colorings V D L) (Fo Fi : V → Finset V), 2 ≤ D → D ≤ Fintype.card V → 1 ≤ L →
      (∀ u h : V, h ∈ Fo u → u ≠ h ∧ Reachable G u h) →
      (∀ v h : V, h ∈ Fi v → h ≠ v ∧ Reachable G h v) →
      (∀ u v : V, IsSeparated G χ u v → ∀ h ∈ Hcirc G u v, h ∈ Fo u ∪ Fi v) →
      (∀ u h : V, h ∈ Fo u → ∀ z ∈ Hcirc G u h, h ∈ Fo z) →
      (∀ v h : V, h ∈ Fi v → ∀ z ∈ Hcirc G h v, h ∈ Fi z) →
      ∃ Tout Tin : V → RootedTree V,
        (∀ h : V, (Tout h).root = h ∧ IsTowardTree G (Tout h) ∧
          (Tout h).verts = insert h (Finset.univ.filter fun u => h ∈ Fo u)) ∧
        (∀ h : V, (Tin h).root = h ∧ IsAwayTree G (Tin h) ∧
          (Tin h).verts = insert h (Finset.univ.filter fun v => h ∈ Fi v)) ∧
        ∑ h, ((Tout h).edges + (Tin h).edges) = ∑ u, (Fo u).card + ∑ v, (Fi v).card ∧
        ∀ u v : V, u ≠ v → IsSeparated G χ u v →
          ∃ x y : V, (x = y ∨ G.Adj x y) ∧ u ∈ (Tout x).verts ∧ v ∈ (Tin y).verts ∧
            dist G u x + (if x = y then 0 else 1) + dist G y v = dist G u v := by sorry

end PredAdvice
