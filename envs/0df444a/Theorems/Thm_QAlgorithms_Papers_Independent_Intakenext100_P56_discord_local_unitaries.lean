-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_local_unitaries
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_local_unitaries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:51:51.90897+00:00
-- url     : https://prove2.me/theorems/e91001fa-3b09-44c9-8a6e-e803f0f2b9b4
-- title:
--   Proposition 19
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   For $\alpha>0$, $\alpha\ne1$, any state $\rho_{AB}$ and arbitrary local unitary operators $U_A,V_B$,
--
--   $$D_\alpha(\bar A;B)_{(U_A\otimes V_B)\rho(U_A\otimes V_B)^\dagger}=D_\alpha(\bar A;B)_\rho.$$
--
--   The full printed order range uses the same defining measurement infimum. This unconditional equality expresses invariance under local changes of orthonormal coordinates.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 17, Proposition 19

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

/-- arXiv:1410.1443v3, PDF p.17, Proposition 19; full printed order range. -/
theorem discord_local_unitaries (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup B ℂ) :
    renyiDiscord a (let W := Matrix.kronecker (U : Op A) (V : Op B); W * rho * Wᴴ) =
      renyiDiscord a rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
