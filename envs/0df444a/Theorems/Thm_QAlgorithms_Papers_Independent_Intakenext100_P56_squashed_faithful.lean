-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_faithful
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_faithful
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:44:07.209753+00:00
-- url     : https://prove2.me/theorems/7cb0aaf6-ffce-48e9-a842-1588f9668f2d
-- title:
--   Remark 9
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume [BSW15a, Conjecture 34] for the actual optimized Petz conditional mutual information, including its von Neumann value at order one. For every $\alpha>1$ and state $\rho_{AB}$,
--
--   $$E^{\rm sq}_\alpha(A;B)_\rho=0\quad\Longleftrightarrow\quad\rho_{AB}\text{ is separable}.$$
--
--   Separability means a finite convex mixture of product densities. The equivalence is the claimed faithfulness property, rather than only vanishing on separable inputs.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 11, Remark 9

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

/-- arXiv:1410.1443v3, PDF p.11, Remark 9. Faithfulness is an iff. -/
theorem squashed_faithful (hconjecture : PetzParameterConjecture) (a : ℝ) (ha : 1 < a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    renyiSquashed a rho = 0 ↔ Entanglement.IsSeparableDensity rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
