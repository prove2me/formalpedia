-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_4
-- name    : ScaleFreeDiam.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:26.869461+00:00
-- url     : https://prove2.me/theorems/0145216d-7f51-433b-9dc7-d2b3137ccd19
-- title:
--   Lemma 4, p. 13 — ℙ(S ⊂ G₁^N) ≤ C^{e(S)} ∏_{ij∈E(S)} 1/√(ij) for an absolute constant C
-- statement:
--   There is an absolute constant $C$ with the following property. Let $S$ be a loopless graph on $[N]$ in which each vertex is joined to at most one earlier vertex and at most two later vertices. Then
--   $$
--   \mathbb P\big(S\subset G_1^N\big)\le C^{e(S)}\prod_{ij\in E(S)}\frac1{\sqrt{ij}},
--   $$
--   where $S\subset G_1^N$ means that every pair of vertices joined in $S$ is joined in $G_1^N$, and $e(S)$ is the number of edges of $S$.
--
--   The lemma compares $G_1^N$ with a random graph in which each edge $ij$ is present independently with probability $C/\sqrt{ij}$; it is the input of the first-moment count of short paths behind the lower bound (Theorem 5).
--
--   **Formalization Note** The bound is the definition `Lemma4Bound C` of the definitions file, which quantifies over all $N$ and all such $S$; $C$ comes first.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 13, Lemma 4

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_4 : ∃ C : ℝ, Lemma4Bound C := by sorry

end ScaleFreeDiam.Main
