-- Prove2me | Theorems.Thm_STCSublinear1377_Main_proposition_1_2
-- name    : STCSublinear1377.Main.proposition_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:20.480654+00:00
-- url     : https://prove2.me/theorems/dbdc5faa-5d57-4ce8-8259-32fd4dd86d7d
-- title:
--   Proposition 1.2 — Polynomial-time baseline with exact constant 8
-- statement:
--   For every connected simple unweighted graph $G$ with $n\ge2$ vertices and $m$ edges, one uniform deterministic polynomial-time algorithm computes a spanning tree $T$ satisfying
--
--   $$c(G,T)\le8\sqrt{mn}.$$
--
--   The number eight is exact. The input contains only the graph, and the output is a full tree adjacency table. This baseline is the deterministic candidate compared against the randomized candidates in Theorem 3.10.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph → a binary adjacency table on Fin n; reason: every finite graph can be enumerated, and symmetry and absence of loops are checked explicitly
--   - encoding: polynomial-time computation → a uniform finite-work-alphabet TM2 evaluator with a polynomial step bound; reason: the evaluator is required to compute the encoded output on every encoded input, so time is tied to actual execution
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Proposition 1.2, PDF/printed p.3; Appendix A.1 p.17

import Definitions.Def_STCSublinear1377_Main_Machine
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Deterministic baseline with the source's exact constant eight. -/
theorem proposition_1_2 :
    ∃ a : BinaryEvaluator, ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g →
      let out := a.eval (graphTapeBits g [])
      let t := outputTable n out
      out.length = n * n ∧ spanning g t ∧
        (congestion g t : ℝ) ≤ 8 * Real.sqrt ((edgeCount g : ℝ) * n) := by sorry

end STCSublinear1377.Main
