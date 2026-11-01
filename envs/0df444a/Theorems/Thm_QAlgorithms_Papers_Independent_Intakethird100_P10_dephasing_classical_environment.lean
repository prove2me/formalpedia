-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P10_dephasing_classical_environment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P10.dephasing_classical_environment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:45:04.954744+00:00
-- url     : https://prove2.me/theorems/5c23c05e-1aec-4db9-9687-f44595f9fa42
-- title:
--   Pauli dephasing has a classical environment in an unbiased basis
-- statement:
--   Let $0\le p\le1$, let $\sigma\in\{X,Y,Z\}$, and use the dilation $V|\psi\rangle=\sqrt{1-p}|\psi\rangle|0\rangle+\sqrt p\sigma|\psi\rangle|1\rangle$. Choose an orthonormal input basis with $\langle\psi_x|\sigma|\psi_x\rangle=0$ for both letters. The complementary outputs are
--
--   $$
--   \operatorname{Tr}_B(V|\psi_x\rangle\langle\psi_x|V^\dagger)=\operatorname{diag}(1-p,p),\qquad x\in\{0,1\},
--   $$
--
--   so they commute. The computational basis for $X$ noise and the Hadamard basis for $Z$ noise give these outputs explicitly as well. The zero-expectation criterion includes $Y$ and avoids using the Pauli eigenbasis.
-- source:
--   Polar codes for degradable quantum channels, arXiv:1109.5346v3, PDF p. 11, Appendix B, unnumbered dephasing-channel classical-environment example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P10

open scoped BigOperators Matrix ComplexConjugate

open Filter

-- Accepted definitions, without paper-local aliases.

open QAlgorithms.Papers.Independent.Information100.P58 (basisDensity)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation)

/-- PDF p.11, Appendix B: the zero-Pauli-expectation (bit-flipping) basis criterion
includes X,Y,Z. Both complement letters equal diag(1-p,p), hence commute.
The source's X computational-basis and Z Hadamard-basis examples are included explicitly. -/
theorem dephasing_classical_environment (p : ℝ) (hlo : 0 ≤ p) (hhi : p ≤ 1)
    (sigma : Matrix Bool Bool ℂ) (hsigma : sigma = pauliX ∨ sigma = pauliY ∨ sigma = pauliZ)
    (basis : Matrix.unitaryGroup Bool ℂ)
    (hunbiased : ∀ x : Bool,
      inner ℂ (basisColumn basis x) (act sigma (basisColumn basis x)) = 0) :
    (∀ x : Bool, dephasingComplement p sigma (pureDensity (basisColumn basis x)) =
      dephasingDiagonal p) ∧
    Commute (dephasingComplement p sigma (pureDensity (basisColumn basis false)))
      (dephasingComplement p sigma (pureDensity (basisColumn basis true))) ∧
    (∀ x : Bool, dephasingComplement p pauliX (basisDensity x) = dephasingDiagonal p) ∧
    (∀ x : Bool, dephasingComplement p pauliZ (pureDensity (act hadamard (ket x))) =
      dephasingDiagonal p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P10

end
