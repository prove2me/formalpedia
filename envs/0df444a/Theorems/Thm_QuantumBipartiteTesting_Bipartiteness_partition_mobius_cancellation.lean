-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_partition_mobius_cancellation
-- name    : QuantumBipartiteTesting.Bipartiteness.partition_mobius_cancellation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:05:35.665795+00:00
-- url     : https://prove2.me/theorems/1b18b849-e129-4987-8c84-8dfcaca73de4
-- title:
--   Möbius cancellation on a strict partition interval
-- statement:
--   Let $p$ and $r$ be partitions of a finite set, with $p$ a proper refinement of $r$. Write $\mu(t,r)$ for the signed refinement-chain coefficient of their partition lattice. Then
--
--   $$
--   \sum_{p\le t\le r}\mu(t,r)=0.
--   $$
--
--   The coefficient includes the empty chain on a diagonal interval and the signed count of chains on each strict interval. This cancellation is the partition inclusion-exclusion identity used to eliminate low-order terms in the matching-moment factorization.
-- source:
--   Ambainis–Childs–Liu, Quantum Property Testing for Bounded-Degree Graphs, https://arxiv.org/pdf/1012.3174, Proposition 5 and §C.4 equation (11), printed pp.7 and20. Used by Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Appendix A.2 equations (A.3), (A.7), pp.30–31.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.partition_mobius_cancellation {k : ℕ}
    (p r : QuantumBipartiteTesting.Bipartiteness.Partition k)
    (hpr : QuantumBipartiteTesting.Bipartiteness.Refines p r) (hne : p ≠ r) :
    (∑ t : QuantumBipartiteTesting.Bipartiteness.Partition k,
      if QuantumBipartiteTesting.Bipartiteness.Refines p t ∧
         QuantumBipartiteTesting.Bipartiteness.Refines t r then
        QuantumBipartiteTesting.Bipartiteness.Mobius t r else 0) = 0 := by sorry
