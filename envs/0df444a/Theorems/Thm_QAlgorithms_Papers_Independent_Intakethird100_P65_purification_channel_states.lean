-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_purification_channel_states
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.purification_channel_states
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:57:50.140099+00:00
-- url     : https://prove2.me/theorems/5feea8be-01f9-4c9e-97e8-d4e89f4d6fcd
-- title:
--   Lemma 10 / Eq.(83): channels from a purification and fixed-marginal states
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $|\psi\rangle_{AR}$ be a normalized pure state, and let $\rho_{AB}$ be a density matrix with $\psi_A=\rho_A$. For every $\varepsilon\ge0$,
--
--   $$\{(\mathrm{id}_A\otimes\mathcal N)(|\psi\rangle\langle\psi|):\mathcal N:R\to B\text{ CPTP},\ P((\mathrm{id}\otimes\mathcal N)(\psi),\rho)\le\varepsilon\}=\{\sigma_{AB}\text{ density}:\sigma_A=\rho_A,\ P(\sigma,\rho)\le\varepsilon\}.$$
--
--   Here $P$ is purified distance. These are sets of states; purification dimension is arbitrary and no full-rank assumption is made.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 19, Lemma 10 / Eq.(83): channels from a purification and fixed-marginal states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Lemma 10, Eq.(83), PDF p.19: equality of sets of STATES, allowing a singular
marginal and arbitrary finite purification dimension R. -/
theorem purification_channel_states (psi : EuclideanSpace ℂ (A × R)) (hpsi : ‖psi‖ = 1)
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (hmarg : traceRight (pureDensity psi) = traceRight rho) (e : ℝ) (he : 0 ≤ e) :
    {sigma : Mat (A × B) | ∃ N : Superop R B, IsChannel N ∧
      sigma = idTensorSuperop N (pureDensity psi) ∧ purifiedDistance sigma rho ≤ e} =
    {sigma : Mat (A × B) | IsDensityMatrix sigma ∧
      purifiedDistance sigma rho ≤ e ∧ traceRight sigma = traceRight rho} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
