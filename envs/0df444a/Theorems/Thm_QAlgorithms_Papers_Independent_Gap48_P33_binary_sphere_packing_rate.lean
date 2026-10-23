-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_binary_sphere_packing_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.binary_sphere_packing_rate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:45:29.500993+00:00
-- url     : https://prove2.me/theorems/482072f1-dfa2-40a0-807c-a9443433fde3
-- title:
--   asymptotic binary sphere-packing rate
-- statement:
--   For each positive integer $n$, let a binary length-$n$ code have $2^{k_n}$ codewords and pairwise disjoint Hamming balls of integer radius $t_n\le n$. Suppose $t_n/n\to p\in[0,1/2]$. Then
--
--   $$\frac{k_n}{n}\le-\frac1n\log_2\sum_{i=0}^{t_n}\binom ni2^{-n},\qquad\limsup_{n\to\infty}\frac{k_n}{n}\le1-H_2(p).$$
--
--   The lower-tail calculation used here is also stated: if $0<r<1$ and $p\le r$, then
--
--   $$-\frac1n\log_2\sum_{i=0}^{t_n}\binom ni r^i(1-r)^{n-i}\longrightarrow D_2(p\|r),$$
--
--   where $D_2(p\|r)=p\log_2(p/r)+(1-p)\log_2((1-p)/(1-r))$. The range $p\le r$, omitted in printed (6.6), is restored. This is the asymptotic packing consequence with integer cutoffs and no rate-convergence assumption.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 14, VI.B, (6.5)–(6.7): asymptotic binary sphere-packing rate

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

/-- PDF pp.13–14, (6.5)–(6.7): integer-cutoff binary sphere packing.
Correction to (6.6): the printed lower-tail exponent omits p<=r; for p>r the
exponent is zero, not D(p||r). Independent moderation of this correction is pending.
The limsup needs no convergence assumption on code rates. -/
theorem binary_sphere_packing_rate (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → BinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (1 / 2) n (t n)) / (n : ℝ)) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤ 1 - binEntropy2 p ∧
    (∀ r : ℝ, 0 < r → r < 1 → p ≤ r →
      Filter.Tendsto (fun n => -Real.logb 2 (binomialLowerTail r n (t n)) / (n : ℝ))
        Filter.atTop (nhds (binaryDivergence p r))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
