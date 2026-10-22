-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_minimal_t_cardinality
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.minimal_t_cardinality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:44:34.107157+00:00
-- url     : https://prove2.me/theorems/742d0521-a6e8-45e0-88a9-68d6fa719061
-- title:
--   Corollary 2: number of operations of exact minimal T-count n
-- statement:
--   Let $M_n$ be the exact matrices admitting a word with at most $n$ $T$ gates, and put $M_{=n}=M_n\setminus M_{n-1}$ for positive $n$. For every positive integer $n$, the set $M_{=n}$ is finite and
--
--   $$|M_{=n}|=576\cdot2^{n-1}.$$
--
--   This counts operations whose minimum possible $T$ count is $n$, rather than words that happen to contain $n$ $T$ symbols. The excluded zero layer has size $192$.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 13, Corollary 2: number of operations of exact minimal T-count n

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.13, Corollary 2: positive exact MINIMAL T-count layers only;
the n=0 layer instead has size 192. -/
theorem minimal_t_cardinality (n : ℕ) (hn : 0 < n) :
    (minimalT n).Finite ∧ (minimalT n).ncard = 576 * 2 ^ (n - 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
