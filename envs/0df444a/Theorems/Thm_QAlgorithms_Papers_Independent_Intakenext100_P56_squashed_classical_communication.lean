-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_squashed_classical_communication
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.squashed_classical_communication
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:38:59.659508+00:00
-- url     : https://prove2.me/theorems/4488b705-8c48-4b4e-b945-cc2fd49bd79b
-- title:
--   Consequence 4
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume Conjecture 1 as stated above. For $\alpha\in(0,1)\cup(1,2]$, a finite probability law $p_x$, and bipartite states $\rho^x_{AB}$, define $\rho_{X_AX_BAB}=\sum_xp_x|x\rangle\langle x|_{X_A}\otimes|x\rangle\langle x|_{X_B}\otimes\rho^x_{AB}$. Then
--
--   $$E^{\rm sq}_\alpha(AX_A;B)_\rho=E^{\rm sq}_\alpha(AX_A;BX_B)_\rho=E^{\rm sq}_\alpha(A;BX_B)_\rho.$$
--
--   The first and last expressions use the corresponding marginals. The infimum defining squashed entanglement still ranges over all extensions. The equality describes invariance under sharing classical information.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 8, Consequence 4

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

/-- arXiv:1410.1443v3, PDF pp.8–9, Consequence 4, (4.3)–(4.4). -/
theorem squashed_classical_communication (hconjecture : LocalMonotonicityConjecture)
    (a : ℝ) (ha : DPOrder a) (p : X → ℝ) (hp : IsLaw p)
    (rho : X → Op (A × B)) (hrho : ∀ x, IsDensityMatrix (rho x)) :
    renyiSquashed a (flagLeft p rho) = renyiSquashed a (flagBoth p rho) ∧
    renyiSquashed a (flagBoth p rho) = renyiSquashed a (flagRight p rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
