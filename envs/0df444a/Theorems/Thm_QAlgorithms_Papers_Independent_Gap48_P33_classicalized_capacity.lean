-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_classicalized_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.classicalized_capacity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:42:44.232528+00:00
-- url     : https://prove2.me/theorems/b9dd5a4a-4951-4e09-887f-584c82efe92f
-- title:
--   maximum classicalized depolarizing information
-- statement:
--   For $0\le p\le1$, let $\rho_{Q'R}(p,q)$ be the measured-input output family in (5.21), with $q\in[0,1]$. Its maximum mutual information is attained at $q=1/2$:
--
--   $$\max_{0\le q\le1} I(R:Q')=I(R:Q')\big|_{q=1/2}=1-H_2(2p/3).$$
--
--   This is the binary symmetric channel value for bit-flip probability $2p/3$, restricted to the family calculated in V.B.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 12, V.B, (5.24): maximum classicalized depolarizing information

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

/-- PDF p.12, (5.24): maximum over the measured-input q-family of V.B only. -/
theorem classicalized_capacity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsGreatest {z : ℝ | ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ z = mutualInformation (classicalOutput p q)}
      (1 - binEntropy2 (2 * p / 3)) ∧
    mutualInformation (classicalOutput p (1 / 2)) = 1 - binEntropy2 (2 * p / 3) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
