-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_le_formation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_le_formation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:49:18.521018+00:00
-- url     : https://prove2.me/theorems/7605e943-1b41-4d61-a48c-fbfd6de4a539
-- title:
--   Proposition 15
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For a state $\rho_{AB}$ and $\alpha\in(0,1)\cup(1,2)$, put $\beta=(2-\alpha)/\alpha$. Then
--
--   $$E^{\rm sq}_\alpha(A;B)_\rho\le E^F_\beta(A;B)_\rho.$$
--
--   Here formation is the infimum of $H_\beta(A|X)$ over all finite normalized pure decompositions. No conjecture is assumed. The order-two endpoint is excluded because it would give formation order zero.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 15, Proposition 15

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

/-- arXiv:1410.1443v3, PDF pp.15–16, Proposition 15, (4.54).
RenyiOrder two is excluded and no conjecture is used. -/
theorem squashed_le_formation (a : ℝ) (ha : RenyiOrder a) (ha2 : a < 2)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    renyiSquashed a rho ≤ renyiFormation ((2-a)/a) rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
