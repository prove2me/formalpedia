-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_pure_squashed_entropy
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.pure_squashed_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:47:45.603396+00:00
-- url     : https://prove2.me/theorems/2c3b5818-427d-4bb1-b4a5-409927111455
-- title:
--   Proposition 13
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For $\alpha\in(0,1)\cup(1,2]$ and any normalized pure bipartite state $\phi_{AB}$,
--
--   $$E^{\rm sq}_\alpha(A;B)_\phi=H_{(2-\alpha)/\alpha}(\phi_A).$$
--
--   Here $H_t(\rho)=\log\operatorname{Tr}(\rho^t)/(1-t)$ and $H_0(\rho)=\log\operatorname{rank}\rho$, using the support-projector convention for $\rho^0$. The identity includes $\alpha=2$ and relates the measure to a marginal Rényi entropy.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 13, Proposition 13

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

/-- arXiv:1410.1443v3, PDF p.13, Proposition 13, (4.43).
At alpha=2 the right side uses H_0 and the support projector. -/
theorem pure_squashed_entropy (a : ℝ) (ha : DPOrder a)
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    renyiSquashed a (pureDensity psi) =
      (renyiEntropySupportNats ((2-a)/a) (traceRight (pureDensity psi)) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
