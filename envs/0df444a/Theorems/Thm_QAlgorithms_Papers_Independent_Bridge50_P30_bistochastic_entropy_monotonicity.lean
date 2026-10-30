-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P30_bistochastic_entropy_monotonicity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P30.bistochastic_entropy_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:33:39.206332+00:00
-- url     : https://prove2.me/theorems/c5af224e-67ac-48d3-bf92-e39f31ebfa56
-- title:
--   Bi-stochastic operations do not decrease von Neumann entropy
-- statement:
--   Let $N\ge1$, let $\rho$ be a positive semidefinite operator of trace one on $\mathbb C^N$, and let $\Phi$ be a complex-linear completely positive trace-preserving map satisfying $\Phi(I)=I$. For von Neumann entropy $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$, with $0\log_2 0=0$, one has
--
--   $$
--   S(\Phi(\rho))\ge S(\rho).
--   $$
--
--   This is entropy monotonicity for bi-stochastic operations on a fixed finite system.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, PDF p. 3, Section 2 opening, unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.3, Section 2 opening: a bi-stochastic operation does not decrease
von Neumann entropy. The displayed source inequality is non-strict. -/
theorem bistochastic_entropy_monotonicity
    {N : ℕ} (hN : 0 < N) (rho : M N) (Phi : Lin N N)
    (hrho : IsDensityMatrix rho) (hPhi : IsBistochastic Phi) :
    vnEntropy rho ≤ vnEntropy (Phi rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P30

end
