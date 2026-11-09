-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_2_10
-- name    : QueryDepthMIS.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:32:31.371798+00:00
-- url     : https://prove2.me/theorems/c3e04fc3-b72b-4a72-9a84-690d7e217627
-- title:
--   Lemma 2.10 — increasing-path bound under a random order on graphs of degree $\le D\log n$
-- statement:
--   For every constant $D$ there is a constant $C$ such that the following holds for every $n \ge 2$. Let $H$ be a simple graph with at most $n$ vertices and maximum degree at most $D \log n$. Under a uniformly random order of its vertices, with probability at least $1 - 1/n^7$ every increasing path of $H$ has at most
--   $$
--   C \log n
--   $$
--   vertices. Here $\log$ is the base-2 logarithm.
--
--   In the proof of Theorem 3.1 this bounds the query depth of the late alive graph, whose degree is $O(\log n)$ by Lemma 2.9.
--
--   Differences from the source:
--   - reading: O(log n) vertices, for a fixed constant D → ∀ D, ∃ C, ∀ n ≥ 2: at most C·log₂ n vertices; reason: the constant hidden in O(·) depends only on D and is uniform in n ≥ 2, the standing assumption of §2.1
--   - encoding: a uniformly random relative order of the vertices of H → a uniform ordering ω : W ≃ Fin |W| with 1-based ranks; reason: the same law
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.10, p.9

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_IsIncreasingPath
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 2.10 (Increasing-path bound [BFS12]) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.10, p.9): "Let H have at most n
vertices and maximum degree at most D log n, for a fixed constant D. Under a uniformly random
relative order of its vertices, the longest increasing path has O(log n) vertices with probability
at least 1 − 1/n⁷."

For every real `D` there is a constant `C` such that for every `n ≥ 2` and every simple graph `H`
on a finite vertex set `W` with `|W| ≤ n` and every degree at most `D log₂ n`, with probability at
least `1 − 1/n⁷` over a uniformly random ordering of `W`, every increasing path of `H` has at most
`C log₂ n` vertices.

**Formalization Note** "O(log n)" is read as `∃ C`, with `C` depending only on `D` and uniform in
`n ≥ 2` (the standing assumption `n ≥ 2`, §2.1, p.7). The random relative order is a uniformly
random `ω : W ≃ Fin |W|` with 1-based ranks; `log` is `Real.logb 2`. -/
theorem lemma_2_10 :
    ∀ D : ℝ, ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        Fintype.card W ≤ n →
        (∀ w : W, (H.degree w : ℝ) ≤ D * Real.logb 2 n) →
        1 - 1 / (n : ℝ) ^ 7 ≤
          PunctSketch.coinProb (fun ω : Perm W => ∀ l : List W, IsIncreasingPath H (rank ω) l →
            (l.length : ℝ) ≤ C * Real.logb 2 n) := by sorry

end QueryDepthMIS
