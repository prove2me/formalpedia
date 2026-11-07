-- Prove2me | Theorems.Thm_PredAdvice_lemma_3_4
-- name    : PredAdvice.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:37.425193+00:00
-- url     : https://prove2.me/theorems/532b5b8a-2c07-4ead-bf13-4e256f1d2aeb
-- title:
--   Lemma 3.4 with eq. (7) — edge-centered 3-hop realization of separated small pairs
-- statement:
--   Let $2\le D\le |V|$ and $L\ge1$, let $\chi_1,\dots,\chi_L$ be any colourings and let $M^{h,j}_{d,c}$ be any maximal matchings of the bipartite graphs $B^{h,j}_{d,c}$, defining $F^{out}_u$, $F^{in}_v$ and $\hat H_F$. For every separated small pair $(u,v)$ with $u\ne v$:
--
--   1. (eq. (7), the coverage property) every $h\in H^\circ_{u,v}$ lies in $F^{out}_u\cup F^{in}_v$;
--   2. $(u,v)$ has an exact edge-centered 3-hop realization using edges of $G$ and hops of $\hat H_F$: there are $x,y$ with $x=u$ or $(u,x)\in E\cup\hat H_F$, with $x=y$ or $(x,y)\in E$, with $y=v$ or $(y,v)\in E\cup\hat H_F$, and
--   $$
--   \mathrm{dist}(u,x)+\mathbf 1_{x\ne y}+\mathrm{dist}(y,v)=\mathrm{dist}(u,v).
--   $$
--
--   Together with Lemma 3.5 this is the core of the hopset construction, and the coverage property is what §4 turns into trees.
--
--   Differences from the source:
--   - generalization: the colourings and matchings fixed in §3.2–3.3 → any colourings and any family of maximal matchings; reason: the proof uses no property of the specific choice; the paper's objects are one instance
--   - encoding: (7): p_i ∈ F^out_u ∪ F^in_v for the internal vertices of a fixed shortest path → every h ∈ H°_{u,v} lies in F^out_u ∪ F^in_v; reason: every h ∈ H°_{u,v} is internal to some shortest path, and p.19 uses (7) in this form
--   - encoding: an edge-centered 3-hop realization, hops with equal endpoints omitted → the alternatives x = u, x = y, y = v and the exact-length identity; reason: the definition of p.5 written out
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 3.4 and eq. (7), p.13

import Mathlib
import Definitions.Def_PredAdvice_HF

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 3.4** with eq. (7) (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.3, p.13). Let `2 ≤ D ≤ n = |V|`, `L ≥ 1`, let
`χ_1, …, χ_L : V → [2D]` be any colourings and let `M^{h,j}_{d,c}` be any maximal matchings of the
bipartite graphs `B^{h,j}_{d,c}`, defining `F^out_u`, `F^in_v` and `Ĥ_F` (eq. (6)). Every
nontrivial separated small pair `(u, v)`

1. (eq. (7), the coverage property) has every interior shortest-path vertex in `F^out_u ∪ F^in_v`;
2. has an exact edge-centered 3-hop realization using edges of `G` and hops of `Ĥ_F`: vertices
   `x, y` with `(u, x)` a hop or an edge or `x = u`, `(x, y) ∈ E` or `x = y`, `(y, v)` a hop or an
   edge or `y = v`, and `dist(u, x) + 1_{x≠y} + dist(y, v) = dist(u, v)`.

**Formalization Note** Eq. (7) is printed for the internal vertices `p_1, …, p_{d−1}` of a fixed
shortest path; it is stated here for every `h ∈ H°_{u,v}`, the union of these over all shortest
paths, which is how p.19 uses it. "Any hop with the same endpoints is allowed to be omitted"
(p.5) is the alternatives `x = u`, `x = y`, `y = v`. -/
theorem lemma_3_4 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ)
      (χ : Colorings V D L) (M : ℕ → ℕ → Fin L → V → Finset (V × V)),
      2 ≤ D → D ≤ Fintype.card V → 1 ≤ L → IsMatchingFamily G χ M →
      ∀ u v : V, u ≠ v → IsSeparated G χ u v →
        (∀ h ∈ Hcirc G u v, h ∈ FOut D M u ∪ FIn D M v) ∧
        ∃ x y : V, (x = u ∨ G.Adj u x ∨ (u, x) ∈ HF D M) ∧ (x = y ∨ G.Adj x y) ∧
          (y = v ∨ G.Adj y v ∨ (y, v) ∈ HF D M) ∧
          dist G u x + (if x = y then 0 else 1) + dist G y v = dist G u v := by sorry

end PredAdvice
