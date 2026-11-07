-- Prove2me | Theorems.Thm_PredAdvice_lemma_4_4
-- name    : PredAdvice.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:51.989088+00:00
-- url     : https://prove2.me/theorems/02a20eb7-ce11-4b58-9022-f536857e53c3
-- title:
--   Lemma 4.4 — tree cover of all reachable pairs by at most $5n$ shortest-path trees
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $G$ be a directed unweighted graph on $n$ vertices and fix integers $2\le D\le n$ and $L\ge1$. There is a family $\mathcal T$ of at most $5n$ shortest-path trees of $G$, each directed toward or away from its root, such that for every reachable ordered pair $(u,v)$ there are $T^-,T^+\in\mathcal T$, directed toward a root $x$ and away from a root $y$, with $x=y$ or $(x,y)\in E$, $u\in V(T^-)$, $v\in V(T^+)$ and
--   $$
--   \mathrm{dist}(u,x)+\mathbf 1_{x\ne y}+\mathrm{dist}(y,v)=\mathrm{dist}(u,v);
--   $$
--   that is, the $u$–$x$ path in $T^-$, the edge $(x,y)$ when $x\ne y$, and the $y$–$v$ path in $T^+$ form a shortest $u$–$v$ path (either tree path may have length zero). Moreover
--   $$
--   \sum_{T\in\mathcal T}|E(T)|\le C\,n^2\Big(\frac{\log D}{D}+\frac1D+\frac{D^2}{2^L}+\frac{LD^2}{RS(n)}\Big). \tag{13}
--   $$
--
--   The tree cover is the execution structure of Theorem 1.1 and also yields the one-missing spanners of Theorem 1.8.
--
--   Differences from the source:
--   - encoding: a family 𝒯 of trees → a list of trees tagged toward/away, of length at most 5n; reason: a list may repeat a tree, which only makes the size bound stronger
--   - encoding: a shortest u–v path formed by two tree paths and an edge → u ∈ V(T⁻), v ∈ V(T⁺) and the exact-length identity; reason: tree paths in shortest-path trees are shortest paths of length dist
--   - encoding: O(·) in (13) → one absolute constant C chosen before V, G, D, L; reason: standard reading of O(·)
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 4.4, eq. (13), p.22

import Mathlib
import Definitions.Def_PredAdvice_RootedTree
import Definitions.Def_PredAdvice_RS

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 4.4** (tree cover for all reachable pairs; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §4.3, eq. (13), p.22). Let `G` be a
directed unweighted graph on `n` vertices and fix integers `2 ≤ D ≤ n` and `L ≥ 1`. There is a
family `𝒯` of at most `5n` shortest-path trees in `G` such that, for every reachable ordered pair
`(u, v)`, there are two trees `T⁻, T⁺ ∈ 𝒯`, directed toward a root `x` and away from a root `y`,
and a shortest `u–v` path formed by the `u–x` path in `T⁻`, the edge `(x, y) ∈ E` when `x ≠ y`, and
the `y–v` path in `T⁺` (either tree path may have length zero). Moreover
`∑_{T ∈ 𝒯} |E(T)| = O(n² (log D/D + 1/D + D²/2^L + L D²/RS(n)))`.

**Formalization Note** The family is a list of trees tagged `toward`/`away`, of length at most
`5n`. The path guarantee is `u ∈ V(T⁻)`, `v ∈ V(T⁺)` and
`dist(u, x) + 1_{x≠y} + dist(y, v) = dist(u, v)` (tree paths of shortest-path trees are shortest
paths of the stated lengths). Reachable pairs include `u = v`. The `O(·)` constant `C` is absolute,
chosen before `V`, `G`, `D`, `L`. -/
theorem lemma_4_4 :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ),
      2 ≤ D → D ≤ Fintype.card V → 1 ≤ L →
      ∃ 𝒯 : List (TreeKind × RootedTree V), 𝒯.length ≤ 5 * Fintype.card V ∧
        (∀ t ∈ 𝒯, (t.1 = .toward → IsTowardTree G t.2) ∧ (t.1 = .away → IsAwayTree G t.2)) ∧
        (∀ u v : V, Reachable G u v → ∃ Tm Tp : RootedTree V,
          (TreeKind.toward, Tm) ∈ 𝒯 ∧ (TreeKind.away, Tp) ∈ 𝒯 ∧
          (Tm.root = Tp.root ∨ G.Adj Tm.root Tp.root) ∧ u ∈ Tm.verts ∧ v ∈ Tp.verts ∧
          dist G u Tm.root + (if Tm.root = Tp.root then 0 else 1) + dist G Tp.root v =
            dist G u v) ∧
        (((𝒯.map fun t => t.2.edges).sum : ℕ) : ℝ) ≤
          C * ((Fintype.card V : ℝ) ^ 2 * (Real.logb 2 D / D + 1 / (D : ℝ) +
            (D : ℝ) ^ 2 / 2 ^ L + (L : ℝ) * (D : ℝ) ^ 2 / RS (Fintype.card V))) := by sorry

end PredAdvice
