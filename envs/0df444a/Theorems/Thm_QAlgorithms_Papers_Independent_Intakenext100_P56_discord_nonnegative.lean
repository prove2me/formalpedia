-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_nonnegative
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_nonnegative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:50:13.9391+00:00
-- url     : https://prove2.me/theorems/67f20833-9649-4a2c-8e3f-7fb281283ec3
-- title:
--   Proposition 17
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For every state $\rho_{AB}$ and $\alpha\in(0,1)\cup(1,2]$,
--
--   $$D_\alpha(\bar A;B)_\rho\ge0.$$
--
--   The bar specifies measurement of $A$. The discord is $\inf_{\{\Lambda_x\}}I_\alpha(E;B|X)_\omega$, where $\omega$ is the actual isometric measurement output and the infimum includes every finite POVM on $A$. This is a pointwise unconditional nonnegativity statement.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 16, Proposition 17

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

/-- arXiv:1410.1443v3, PDF p.16, Proposition 17; measured register A. -/
theorem discord_nonnegative (a : ℝ) (ha : DPOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) : 0 ≤ renyiDiscord a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
