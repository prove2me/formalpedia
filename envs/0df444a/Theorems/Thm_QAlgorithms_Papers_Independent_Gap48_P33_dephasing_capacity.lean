-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_dephasing_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.dephasing_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:44:42.176986+00:00
-- url     : https://prove2.me/theorems/dfc326d1-85d0-4342-96d8-d3a8be9b1f7a
-- title:
--   dephasing maximum mutual information
-- statement:
--   Let $0\le p\le1$ and $\mathcal D_p(\rho)=(1-p)\rho+pZ\rho Z^*$. For normalized qubit inputs, with information evaluated using an unchanged purifying reference,
--
--   $$\max_\rho I(\mathcal D_p,\rho)=I(\mathcal D_p,\mathbf1/2)=2-H_2(p).$$
--
--   Both computational-basis states are fixed by $\mathcal D_p$, so classical basis bits are transmitted without error for every $p$. At $p=1/2$ the displayed maximum equals one bit. This states the channel calculation without assuming a general separation of capacities.
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 13, VI.A, (6.3): dephasing maximum mutual information

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

/-- PDF p.13, (6.3): all-density dephasing maximum and error-free computational bits. -/
theorem dephasing_capacity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsGreatest (informationValues (phaseFlipChannel p)) (2 - binEntropy2 p) ∧
    inputMutualInfo (phaseFlipChannel p) (diagonalSource (1 / 2)) = 2 - binEntropy2 p ∧
    (∀ b : Bool, phaseFlipChannel p (pureDensity (ket b)) = pureDensity (ket b)) ∧
    inputMutualInfo (phaseFlipChannel (1 / 2)) (diagonalSource (1 / 2)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
