-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_joint_convexity_remainder_and_equivalence
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.joint_convexity_remainder_and_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:57:04.581527+00:00
-- url     : https://prove2.me/theorems/4b17ac38-6ea9-490c-a0bb-694a53917429
-- title:
--   Consequence 28
-- statement:
--   All registers are finite-dimensional and logarithms are natural. For probability weights $p_x$ and positive definite density matrices $\rho_x,\sigma_x$, set $\bar\rho=\sum_xp_x\rho_x$, $\bar\sigma=\sum_xp_x\sigma_x$, and $R_x=\sigma_x^{1/2}\bar\sigma^{-1/2}\bar\rho\bar\sigma^{-1/2}\sigma_x^{1/2}$. Conjecture 26 implies the universal joint-convexity remainder inequality
--
--   $$\sum_xp_xD(\rho_x\Vert\sigma_x)-D(\bar\rho\Vert\bar\sigma)\ge-2\log\sum_xp_x\sqrt{F(\rho_x,R_x)}.$$
--
--   Independently of Conjecture 26, this universal inequality is equivalent to the universal relative-entropy recovery inequality (6.24), on its positive definite state and strict CPTP channel domain. Here $F$ is squared fidelity, extended to positive recovered operators without normalizing them; the square root is inside the weighted sum.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 27, Consequence 28

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

/-- arXiv:1410.1443v3, PDF pp.27–29, Consequence 28, (6.28).
The quantitative bound assumes Conjecture 26. The equivalence between the
UNIVERSAL inequality schemes is unconditional, as its two-direction proof shows. -/
theorem joint_convexity_remainder_and_equivalence :
    (DifferenceParameterConjecture → JointRemainder) ∧
      (JointRemainder ↔ RecoveryRemainder) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
