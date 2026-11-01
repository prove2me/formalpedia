-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_formation_min_formula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.formation_min_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:46:18.353671+00:00
-- url     : https://prove2.me/theorems/0d15e4c7-4d1e-4af2-9b7e-1fe4c20e4576
-- title:
--   Proposition 12
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\alpha>0$, $\alpha\ne1$, and let $\rho_{AB}$ be a state. The Rényi entanglement of formation, defined as the infimum of $H_\alpha(A|X)$ over finite pure decompositions, obeys
--
--   $$E^F_\alpha(A;B)_\rho=\min_{\rho=\sum_xp_x|\psi_x\rangle\langle\psi_x|}\frac{\alpha}{1-\alpha}\log\sum_xp_x\left[\operatorname{Tr}((\psi_A^x)^\alpha)\right]^{1/\alpha}.$$
--
--   Each $p_x$ is nonnegative, the weights sum to one, $|\psi_x\rangle$ is normalized, and $\psi_A^x=\operatorname{Tr}_B|\psi_x\rangle\langle\psi_x|$. The minimum is attained by some finite ensemble; no cardinality bound is asserted. The outer weights are $p_x$, not $p_x^\alpha$.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 12, Proposition 12

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

/-- arXiv:1410.1443v3, PDF pp.12–13, Proposition 12, (4.38).
The value equals an ATTAINED minimum, with no cardinality bound. -/
theorem formation_min_formula (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    ∃ ens : FinitePureDecomposition rho,
      renyiFormation a rho = (formationObjective a ens : EReal) ∧
      ∀ other : FinitePureDecomposition rho, formationObjective a ens ≤ formationObjective a other := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
