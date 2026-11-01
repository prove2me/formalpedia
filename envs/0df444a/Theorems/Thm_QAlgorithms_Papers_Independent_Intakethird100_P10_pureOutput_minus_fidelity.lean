-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_pureOutput_minus_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.pureOutput_minus_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:41:13.720522+00:00
-- url     : https://prove2.me/theorems/c04b9b50-6f2d-4c88-9125-be12ca847d1c
-- title:
--   Pure-output minus transform preserves squared fidelity
-- statement:
--   Let $|\psi_0\rangle,|\psi_1\rangle$ be normalized vectors on a common finite nonempty register, and put $W(x)=|\psi_x\rangle\langle\psi_x|$. Construct $W^-$ with letter states
--
--   $$
--   \rho_0^-={1\over2}(\rho_0\otimes\rho_0+\rho_1\otimes\rho_1),\qquad
--   \rho_1^-={1\over2}(\rho_0\otimes\rho_1+\rho_1\otimes\rho_0).
--   $$
--
--   Then the squared Uhlmann fidelities satisfy
--
--   $$
--   F(W)=|\langle\psi_0|\psi_1\rangle|^2=F(W^-).
--   $$
--
--   Distinctness and orthogonality are not assumed. This equality identifies why the classical poor-channel inequality can fail for quantum pure outputs.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 10, Theorem 9: pure-output minus transform preserves fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.10, Theorem 9: squared fidelity is squared overlap for pure letters,
and is unchanged by the explicitly constructed worse branch.
Coincident and orthogonal normalized vectors are both allowed. -/
theorem pureOutput_minus_fidelity {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    (psi0 psi1 : EuclideanSpace ℂ H) (h0 : IsState psi0) (h1 : IsState psi1) :
    squaredFidelity (pureCQ psi0 psi1 false) (pureCQ psi0 psi1 true) = ‖inner ℂ psi0 psi1‖ ^ 2 ∧
    squaredFidelity (pureCQ psi0 psi1 false) (pureCQ psi0 psi1 true) =
      squaredFidelity (minusChannel (pureCQ psi0 psi1) false)
        (minusChannel (pureCQ psi0 psi1) true) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
