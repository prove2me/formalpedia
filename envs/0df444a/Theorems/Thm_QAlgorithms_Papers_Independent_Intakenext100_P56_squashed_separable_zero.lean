-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_separable_zero
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_separable_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:42:57.802227+00:00
-- url     : https://prove2.me/theorems/bd7a7ec0-8e69-4427-9e7b-be41ac3beea3
-- title:
--   Proposition 8
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\alpha>0$ with $\alpha\ne1$. A separable bipartite state is any finite convex mixture of product density operators. For every such state,
--
--   $$E^{\rm sq}_\alpha(A;B)_\rho=0.$$
--
--   This is unconditional, including orders greater than two. It gives the vanishing direction of faithfulness.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 10, Proposition 8

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

/-- arXiv:1410.1443v3, PDF pp.10–11, Proposition 8. Full positive-order range. -/
theorem squashed_separable_zero (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho)
    (hsep : Entanglement.IsSeparableDensity rho) : renyiSquashed a rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
