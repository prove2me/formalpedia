-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_rank_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_rank_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:52:32.537024+00:00
-- url     : https://prove2.me/theorems/95b60bf0-133c-4efa-b64b-bf45f6f379f6
-- title:
--   Proposition 20
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For $\alpha\in(0,1)\cup(1,2]$ and every state $\rho_{AB}$,
--
--   $$D_\alpha(\bar A;B)_\rho=\inf_{\sum_x|\varphi_x\rangle\langle\varphi_x|=I_A}I_\alpha(E;B|X)_{\omega^{\varphi}}.$$
--
--   The right side uses arbitrary finite rank-one POVMs and their actual measurement dilations. The kets need not be normalized or mutually orthogonal, and zero effects can be deleted. The assertion equates infima and does not assert attainment.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 17, Proposition 20

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

/-- arXiv:1410.1443v3, PDF pp.17–18, Proposition 20: equality of infima. -/
theorem discord_rank_one (a : ℝ) (ha : DPOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    renyiDiscord a rho = rankOneDiscord a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
