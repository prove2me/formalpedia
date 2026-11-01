-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_product_subadditive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_product_subadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:45:15.27599+00:00
-- url     : https://prove2.me/theorems/f3771c3a-81f8-4754-9cf7-def0b5ae5e38
-- title:
--   Proposition 10
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\alpha>0$, $\alpha\ne1$, and let $\sigma_{A_1B_1}$ and $\tau_{A_2B_2}$ be independent states. Regroup their tensor product as $\rho_{A_1A_2B_1B_2}=\sigma\otimes\tau$. Then
--
--   $$E^{\rm sq}_\alpha(A_1A_2;B_1B_2)_\rho\le E^{\rm sq}_\alpha(A_1;B_1)_\sigma+E^{\rm sq}_\alpha(A_2;B_2)_\tau.$$
--
--   The extension dimensions of the two factors are independent. This is subadditivity on product states; it does not assert equality or superadditivity.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 11, Proposition 10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

open scoped Matrix.Norms.L2Operator

/-- arXiv:1410.1443v3, PDF p.11, Proposition 10, (4.30): SUBadditivity. -/
theorem squashed_product_subadditive (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × B)) (sigma : Op (C × D))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    renyiSquashed a (bipartiteProduct rho sigma) ≤
      renyiSquashed a rho + renyiSquashed a sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
