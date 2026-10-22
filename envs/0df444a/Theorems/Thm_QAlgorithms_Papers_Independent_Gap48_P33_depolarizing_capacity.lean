-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_depolarizing_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.depolarizing_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:30:28.756471+00:00
-- url     : https://prove2.me/theorems/2cd87a1f-7568-4bf3-890c-6b9beb539e76
-- title:
--   von Neumann capacity of the Pauli depolarizing channel
-- statement:
--   Let $0\le p\le1$, and let $\mathcal N_p(\rho)=(1-p)\rho+\frac p3(X\rho X^*+Y\rho Y^*+Z\rho Z^*)$. For any normalized qubit density $\rho$, purify it by a reference $R$ and write $I(\mathcal N,\rho)=S(R:Q')$, where the channel acts only on the signal and $S$ is entropy in bits. Then
--
--   $$C_Q(\mathcal N_p)=\max_{\rho}I(\mathcal N_p,\rho)=I(\mathcal N_p,\mathbf1/2)=2-H_2(p)-p\log_2 3.$$
--
--   Here $H_2$ is binary entropy, with $0\log 0=0$. This value vanishes exactly at $p=3/4$ and equals two bits at $p=0$. This is the paper's maximum mutual-information calculation.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 11, V.A, (5.18): von Neumann capacity of the Pauli depolarizing channel

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

/-- PDF p.11, (5.18), using the ALL-density maximum of p.5, (3.15). -/
theorem depolarizing_capacity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsGreatest (informationValues (pauliDepolarizing p))
      (2 - binEntropy2 p - p * Real.logb 2 3) ∧
    inputMutualInfo (pauliDepolarizing p) (diagonalSource (1 / 2)) =
      2 - binEntropy2 p - p * Real.logb 2 3 ∧
    (2 - binEntropy2 p - p * Real.logb 2 3 = 0 ↔ p = 3 / 4) ∧
    inputMutualInfo (pauliDepolarizing 0) (diagonalSource (1 / 2)) = 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
