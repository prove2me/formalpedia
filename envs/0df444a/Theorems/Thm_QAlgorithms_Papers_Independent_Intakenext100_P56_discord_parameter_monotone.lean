-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_parameter_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_parameter_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:00:44.675982+00:00
-- url     : https://prove2.me/theorems/f8f862c0-9119-44de-84d2-6ef85bc22924
-- title:
--   Unnumbered: Table 2 conditional monotonicity of discord in alpha
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume [BSW15a, Conjecture 34] for the optimized Petz conditional mutual information appearing in (3.18), including the ordinary value at one. For every state $\rho_{AB}$ and positive orders $\alpha\le\beta$, with the same measurement-infimum formula and its continuous one endpoint,
--
--   $$D_\alpha(\bar A;B)_\rho\le D_\beta(\bar A;B)_\rho.$$
--
--   In particular this includes the common domain of Definition 16. It is a conditional order comparison and does not assert the conjecture.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 19, Unnumbered: Table 2 conditional monotonicity of discord in alpha

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

/-- arXiv:1410.1443v3, PDF p.19, Table 2: conditional order monotonicity
of Definition 16, under the OPTIMIZED PETZ parameter conjecture. -/
theorem discord_parameter_monotone (hconjecture : PetzParameterConjecture)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    renyiDiscord a rho ≤ renyiDiscord b rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
