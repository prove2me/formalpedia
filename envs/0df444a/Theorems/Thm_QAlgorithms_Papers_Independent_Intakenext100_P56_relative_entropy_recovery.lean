-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_relative_entropy_recovery
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.relative_entropy_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:56:22.135988+00:00
-- url     : https://prove2.me/theorems/a3e34e4a-e210-4e8e-a5a9-fb054534f9b1
-- title:
--   Consequence 27
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume Conjecture 26, namely parameter monotonicity of both actual relativeEntropyDifference functionals (6.12)–(6.13), including their value at one. Let $\rho,\sigma$ be positive definite density operators and $\mathcal N$ a strict CPTP map. Define $\mathcal T(Z)=\sigma^{1/2}\mathcal N^\dagger[\mathcal N(\sigma)^{-1/2}Z\mathcal N(\sigma)^{-1/2}]\sigma^{1/2}$. This map is CPTP and
--
--   $$D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))\ge-\log F(\rho,\mathcal T(\mathcal N(\rho))).$$
--
--   The relative entropy is Umegaki entropy in nats, and $F$ is squared fidelity. This retains the normalization of the headline (6.24).
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 26, Consequence 27

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

/-- arXiv:1410.1443v3, PDF p.26, Consequence 27, (6.23)–(6.24).
Squared fidelity follows the headline; (6.26) drops a factor two by typo. -/
theorem relative_entropy_recovery (hconjecture : DifferenceParameterConjecture)
    (rho sigma : Op A) (N : Superop A B)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef) (hN : StrictChannel N) :
    IsChannel (petz sigma N) ∧
      -extendedLog (squaredFidelity rho (petz sigma N (N rho))) ≤ (relativeEntropyDifference rho sigma N : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
