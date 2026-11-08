-- Prove2me | Theorems.Thm_SkewMatching_lemma_21
-- name    : SkewMatching.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:08:46.143675+00:00
-- url     : https://prove2.me/theorems/bd8a4ca1-e460-44b2-b824-1d72fc060406
-- title:
--   Lemma 21 — the number of copies of an edge in the cut is |h(u) − h(v)|
-- statement:
--   Let $h$ be a function on the vertices of a directed graph $G_1$ with values in $\{-1,0,1\}$, and let $S=\{u^0:h(u)\ge 0\}\cup\{u^1:h(u)\ge 1\}$ in the graph $G_2$ with two copies of each vertex and two copies $(u^0,v^0)$, $(u^1,v^1)$ of each edge. Then for any edge $(u,v)$ of $G_1$, the number of copies of this edge in $\partial S$ is exactly
--
--   $$
--   |h(u)-h(v)|.
--   $$
--
--   Thus a uniform sample over cut edges of $G_2$ samples edges of $G_1$ proportionally to their height difference.
--
--   Differences from the source:
--   - encoding: any edge (u, v) of a directed graph G₁ → any pair of vertices u, v; reason: every pair is an edge of some directed graph, and the count depends only on the two heights
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 21, p.13

import Mathlib
import Definitions.Def_SkewMatching_heightCut

namespace SkewMatching

open scoped Classical

/-- **Lemma 21**, p.13. "Let G₁ be any directed graph with vertex heights h ∈ {−1, 0, 1}. Define an undirected graph G₂ as follows: For each vertex u in G₁, create two vertices u⁰ and u¹ in G₂. For each edge (u, v) in G₁, add two copies (u⁰, v⁰) and (u¹, v¹) of this edge in G₂. Let S be the following set defined by vertex heights h: S = {u⁰ : h(u) ≥ 0} ∪ {u¹ : h(u) ≥ 1}.
Then for any edge (u, v) in G₁, the number of copies of this edge in the cut ∂S is exactly |h(u) − h(v)|."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 21, p.13.

**Formalization Note.** `u`, `v` are the ends of an edge of `G₁`, and its copies are indexed by `i : Fin 2`. A copy `(uⁱ, vⁱ)` is in `∂S` when exactly one of its ends is in `S`. Any pair `(u, v)` is an edge of some directed graph, so the graph needs no separate object. -/
theorem lemma_21 {V : Type*} (h : V → ℤ) (hh : ∀ u, h u = -1 ∨ h u = 0 ∨ h u = 1) (u v : V) :
    (((Finset.univ : Finset (Fin 2)).filter fun i =>
        ((u, i) ∈ heightCut h) ≠ ((v, i) ∈ heightCut h)).card : ℤ) = |h u - h v| := by sorry

end SkewMatching
