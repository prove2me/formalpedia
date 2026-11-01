-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_discord_cq_zero
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.discord_cq_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:51:09.036496+00:00
-- url     : https://prove2.me/theorems/3c7db654-459e-4c0e-9d78-fc4275ee3184
-- title:
--   Proposition 18
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\alpha>0$, $\alpha\ne1$. If $\rho_{AB}$ is classical on $A$, meaning $\rho_{AB}=\sum_xp_x|u_x\rangle\langle u_x|_A\otimes\rho_B^x$ for an orthonormal basis of $A$, a probability law $p$, and states $\rho_B^x$, then
--
--   $$D_\alpha(\bar A;B)_\rho=0.$$
--
--   The identical infimum formula (5.1) is used at all printed orders. The proof's use of Proposition 17 above order two is a recorded source gap, not an added nonnegativity hypothesis.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 16, Proposition 18

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

/-- arXiv:1410.1443v3, PDF pp.16–17, Proposition 18.
Retains printed alpha>2 range by the identical (5.1) formula; the proof's
use of Proposition 17 beyond its range is recorded as a source proof gap. -/
theorem discord_cq_zero (a : ℝ) (ha : RenyiOrder a)
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) (hcq : IsClassicalOnA rho) :
    renyiDiscord a rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
