-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_ordinary_hamming_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.ordinary_hamming_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:46:15.870092+00:00
-- url     : https://prove2.me/theorems/f85e69fe-c68b-4f66-88dc-741e582735cf
-- title:
--   ordinary nondegenerate quantum Hamming rate
-- statement:
--   For every positive $n$, let an exact nondegenerate n-qubit code have dimension $2^{k_n}$, correcting all phase-free Pauli errors of weight at most the integer $t_n\le n$. Explicitly, distinct message codewords and distinct such errors have orthonormal error descendants. If $t_n/n\to p\in[0,3/4]$, then
--
--   $$2^{k_n}\sum_{i=0}^{t_n}3^i\binom ni\le2^n,$$
--   $$\frac{k_n}{n}\le-\frac1n\log_2\sum_{i=0}^{t_n}\binom ni(3/4)^i(1/4)^{n-i}-1,$$
--   $$\limsup_{n\to\infty}\frac{k_n}{n}\le1-H_2(p)-p\log_2 3.$$
--
--   The finite Hamming inequality is cited background [8–10]; the finite logarithmic and asymptotic consequences are (6.9)–(6.10). Negative upper rates are retained and exclude such a family.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 14, VI.B, (6.9)–(6.10): ordinary nondegenerate quantum Hamming rate

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

/-- PDF p.14, (6.8)–(6.10): ordinary NONDEGENERATE exact-code bound.
The finite Hamming premise is background [8–10]. The lower-tail range p<=3/4
is restored; negative upper rates are not clipped. -/
theorem ordinary_hamming_rate (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 3 / 4)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → OrdinaryCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    (∀ n, 0 < n → 2 ^ k n * ballVolume 3 n (t n) ≤ 2 ^ n) ∧
    (∀ n, 0 < n → messageRate (k n) n ≤
      -Real.logb 2 (binomialLowerTail (3 / 4) n (t n)) / (n : ℝ) - 1) ∧
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤
      1 - binEntropy2 p - p * Real.logb 2 3 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
