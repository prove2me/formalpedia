-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_lemma_2
-- name    : ScaleFreeDiam.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:43.378164+00:00
-- url     : https://prove2.me/theorems/b0d114cb-df8f-4cde-903b-3cc39eaa62be
-- title:
--   Lemma 2, p. 10 — ℙ(g_j = i) = O((ij)^{−1/2}) and ℙ(g_j = i, g_k = i) = O(i^{−1}(jk)^{−1/2})
-- statement:
--   In the process $G_1^N$, let $g_j$ be the vertex to which vertex $j$ sends its edge. There is an absolute constant $C$ such that for all $N$ and all $1\le i<j\le N$,
--   $$
--   \mathbb P(g_j=i)\le C\,(ij)^{-1/2},
--   $$
--   and for all $1\le i<j<k\le N$,
--   $$
--   \mathbb P(g_j=i,\ g_k=i)\le C\,i^{-1}(jk)^{-1/2}.
--   $$
--   These estimates make the dependence in $G_1^N$ quantitative: an edge $ij$ appears with probability comparable to $1/\sqrt{ij}$, as in an inhomogeneous random graph. They feed Lemma 4.
--
--   **Formalization Note** The paper's $O(\cdot)$ constants are "absolute constants" (p. 10), so $C$ is quantified before $N,i,j,k$.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 10, Lemma 2, (1)–(2)

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem lemma_2 :
    ∃ C : ℝ,
      (∀ N i j : ℕ, 1 ≤ i → i < j → j ≤ N →
        probG1 N (fun g => tgt g j = i) ≤ C * ((i : ℝ) * j) ^ (-(1 / 2 : ℝ))) ∧
      (∀ N i j k : ℕ, 1 ≤ i → i < j → j < k → k ≤ N →
        probG1 N (fun g => tgt g j = i ∧ tgt g k = i) ≤
          C * (i : ℝ)⁻¹ * ((j : ℝ) * k) ^ (-(1 / 2 : ℝ))) := by sorry

end ScaleFreeDiam.Main
