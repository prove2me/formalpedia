-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_atypical_entropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.atypical_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:24:50.198721+00:00
-- url     : https://prove2.me/theorems/7e95f8eb-d6ea-46bb-9865-d11858904e04
-- title:
--   Supplementary Note 6: atypical-sector entropy contribution
-- statement:
--   Let $p$ be a normalized nonnegative spectral probability distribution on the $4^N$-dimensional space of $N$ pairs. Let $A$ be the set of eigenvectors assigned to the atypical sector, and suppose $\sum_{i\in A}p_i\le\epsilon$ with $0\le\epsilon\le e^{-1}$. Using $0\log0=0$, its contribution to the entropy obeys
--
--   $$S_A=-\sum_{i\in A}p_i\log_2p_i\le-\epsilon\log_2\!\left(\frac\epsilon{4^N}\right).$$
--
--   The exact bound includes the term $\epsilon\log_2(1/\epsilon)$. The sector is spectral, rather than an arbitrary noncommuting projection.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 21, Supplementary Note 6: atypical-sector entropy contribution

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.21: the exact atypical-sector bound, without the uncontrolled approximation
2N epsilon. Here p is the spectral distribution after the classical reduction. -/
theorem atypical_entropy (N : ℕ) (p : PairRegister N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hnorm : ∑ i, p i = 1) (S : Finset (PairRegister N))
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hsmall : epsilon ≤ Real.exp (-1))
    (hmass : ∑ i ∈ S, p i ≤ epsilon) :
    spectralContribution p S ≤ -epsilon * Real.logb 2 (epsilon / (2 : ℝ) ^ (2 * N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
