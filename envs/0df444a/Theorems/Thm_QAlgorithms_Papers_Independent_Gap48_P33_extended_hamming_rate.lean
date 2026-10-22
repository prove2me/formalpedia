-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_extended_hamming_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.extended_hamming_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:47:41.019601+00:00
-- url     : https://prove2.me/theorems/70ebc8e9-fa24-4934-89ad-f3180d2936b6
-- title:
--   asymptotic extended Hamming rate
-- statement:
--   For every positive $n$, take an extended orthogonal error code of (6.11), with $2^{k_n}$ messages in a noiseless n-qubit reference and an n-qubit signal. All Pauli-error descendants of weight at most the integer $t_n\le n$ are orthonormal. If $t_n/n\to p\in[0,3/4]$, then
--
--   $$\limsup_{n\to\infty}\frac{k_n}{n}\le2-H_2(p)-p\log_2 3=C_Q(\mathcal N_p).$$
--
--   Here the final value is the attained all-density maximum of channel mutual information. This retains the exact nondegenerate assumptions of the counting argument, without asserting the following unrestricted operational converse.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 14, VI.B, (6.12): asymptotic extended Hamming rate

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

/-- PDF p.14, (6.12): SAME exact orthogonal codes, corrected lower-tail range.
The subsequent unrestricted weak converse is separately deferred. -/
theorem extended_hamming_rate (k t : ℕ → ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 3 / 4)
    (ht : ∀ n, 0 < n → t n ≤ n)
    (hcode : ∀ n, 0 < n → ExtendedCode n (k n) (t n))
    (hlimit : Filter.Tendsto (fun n => messageRate (t n) n) Filter.atTop (nhds p)) :
    Filter.limsup (fun n => messageRate (k n) n) Filter.atTop ≤
      2 - binEntropy2 p - p * Real.logb 2 3 ∧
    IsGreatest (informationValues (pauliDepolarizing p))
      (2 - binEntropy2 p - p * Real.logb 2 3) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
