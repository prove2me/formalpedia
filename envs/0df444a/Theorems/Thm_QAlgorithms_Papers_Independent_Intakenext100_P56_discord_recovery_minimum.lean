-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_recovery_minimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_recovery_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:54:48.752528+00:00
-- url     : https://prove2.me/theorems/d6609cbe-97f4-49b3-ad32-02941ea3f010
-- title:
--   Consequence 23
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume the sandwiched conditional-information parameter conjecture (5.41), including its value at one. For any state $\rho_{AB}$,
--
--   $$D(\bar A;B)_\rho\ge\min_{\sum_x|\varphi_x\rangle\langle\varphi_x|=I_A}-\log F\bigl(\rho_{AB},(\mathcal E_{\rho_A,\varphi}\otimes\mathrm{id}_B)(\rho_{AB})\bigr).$$
--
--   Here $F$ is squared Uhlmann fidelity. With $q_x=\langle\varphi_x|\rho_A|\varphi_x\rangle$, the map prepares $\rho_A^{1/2}|\varphi_x\rangle\langle\varphi_x|\rho_A^{1/2}/q_x$ after outcome $x$ when $q_x>0$, and prepares $\rho_A$ otherwise. It is a single entanglement-breaking map. The minimum is attained; $-\log0=+\infty$, and full rank is not required.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 22, Consequence 23

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

/-- arXiv:1410.1443v3, PDF pp.22–23, Consequence 23, (5.47).
The minimum is attained; rho_A need not be invertible. -/
theorem discord_recovery_minimum (hconjecture : SandwichedParameterConjecture)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    ∃ m : ℕ, 0 < m ∧ ∃ phi : Fin m → EuclideanSpace ℂ A,
      KetPOVM phi ∧ discordRecoveryCost rho phi ≤ renyiDiscord 1 rho ∧
      ∀ n : ℕ, 0 < n → ∀ other : Fin n → EuclideanSpace ℂ A,
        KetPOVM other → discordRecoveryCost rho phi ≤ discordRecoveryCost rho other := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
