-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_partition_power_sum_cancellation
-- name    : QuantumBipartiteTesting.Bipartiteness.partition_power_sum_cancellation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:12:25.20721+00:00
-- url     : https://prove2.me/theorems/48e0c994-ead0-4e15-a7a8-8bd9c98d9301
-- title:
--   Low-weight partition power sums have vanishing Möbius average
-- statement:
--   Let $p$ be a partition of a set of $k$ elements, and let $d_{i,j}$ be arbitrary real numbers indexed by an element $i$ and one of finitely many colors $j$. For a positive integer $a$ and a partition $r$, define
--
--   $$
--   S_a(r)=\sum_{B\in r}\sum_j\left(\sum_{i\in B}d_{i,j}\right)^a.
--   $$
--
--   Let $a_1,\ldots,a_m$ be positive integers satisfying
--
--   $$
--   \sum_{t=1}^m(a_t-1)<k-|p|.
--   $$
--
--   Then the signed refinement-chain coefficients satisfy
--
--   $$
--   \sum_{r\le p}\mu(r,p)\prod_{t=1}^m S_{a_t}(r)=0.
--   $$
--
--   This is the polynomial cancellation identity underlying the extra power of the block parameter in the matching-moment numerator. It applies in particular to the component-color edge counts used in the source factorization.
-- source:
--   Ambainis–Childs–Liu, Quantum Property Testing for Bounded-Degree Graphs, https://arxiv.org/pdf/1012.3174, Proposition 19, §C.5 equation (13), printed pp.20–21; used in Proposition 6, pp.8–9. The polynomial identity is proved for arbitrary real entries, extending the nonnegative component-count entries used there. Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Appendix A.2 equation (A.7), pp.30–31.

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.partition_power_sum_cancellation {k colors m : ℕ}
    (p : QuantumBipartiteTesting.Bipartiteness.Partition k) (a : Fin m → ℕ)
    (ha : ∀ t, 0 < a t) (d : Fin k → Fin colors → ℝ)
    (hbudget : (∑ t, (a t-1))+(QuantumBipartiteTesting.Bipartiteness.Blocks p).card < k) :
    (∑ r : QuantumBipartiteTesting.Bipartiteness.Partition k,
      if QuantumBipartiteTesting.Bipartiteness.Refines r p then
        (QuantumBipartiteTesting.Bipartiteness.Mobius r p:ℝ) *
          (∏ t : Fin m, ∑ S ∈ QuantumBipartiteTesting.Bipartiteness.Blocks r,
            ∑ j : Fin colors, (∑ i ∈ S, d i j)^(a t)) else 0) = 0 := by sorry
