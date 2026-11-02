-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P75_two_qubit_operator_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P75.two_qubit_operator_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:04:05.20431+00:00
-- url     : https://prove2.me/theorems/6653361e-c0f7-4ce9-b119-b6e5ca489dd3
-- title:
--   Two operator identities suffice for exact qubit extraction
-- statement:
--   Let \(H_A,H_B\) be arbitrary complex Hilbert spaces and \(|\psi'\rangle\) a normalized vector in their completed Hilbert tensor product. Let \(X_A,Z_A,X_B,Z_B\) be local bounded self-adjoint involutions, and let \(0\leq\theta\leq\pi/4\). Suppose
--   \[
--   Z_A|\psi'\rangle=Z_B|\psi'\rangle,\qquad
--   \sin\theta\,X_A(I+Z_B)|\psi'\rangle
--   =\cos\theta\,X_B(I-Z_A)|\psi'\rangle.
--   \]
--   For \(D=A,B\), define the fixed complex-linear map
--   \[
--   V_Dv=\frac{(I+Z_D)v\otimes|0\rangle+
--   X_D(I-Z_D)v\otimes|1\rangle}{2},\qquad
--   |q\rangle=\frac{I+Z_A}{2\cos\theta}|\psi'\rangle.
--   \]
--   Both \(V_D\) are isometric embeddings, \(q\) has norm one, and, after fixed register regrouping,
--   \[
--   (V_A\otimes V_B)|\psi'\rangle
--   =|q\rangle\otimes(\cos\theta|00\rangle+\sin\theta|11\rangle).
--   \]
--   This is an operator sufficient condition for the Figure 1 state-extraction circuit. No within-party anticommutation assumption or measurement-certification conclusion is appended. At \(\theta=0\), it extracts the product state \(|00\rangle\).
-- source:
--   Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States, arXiv:1210.4409v2, PDF p. 2, §III, (4) and Fig.1: sufficient operator identities for exact two-qubit extraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P75

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P75

universe u v w x

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

section ExtractionStatements

variable {H : Type u} {K : Type v}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- PDF p.2, (4), Fig.1, expanded p.8, (26): exact extraction by the specified
local maps, without within-party anticommutation assumptions. The normalized
witness is exactly (30); theta=0 is included literally. -/
theorem two_qubit_operator_criterion (theta : ℝ) (htheta : 0 ≤ theta)
    (hthetaUpper : theta ≤ Real.pi / 4)
    (psi : HilbertTensor H K) (hpsi : ‖psi‖ = 1)
    (XA ZA : H →L[ℂ] H) (XB ZB : K →L[ℂ] K)
    (hXA : Dichotomic XA) (hZA : Dichotomic ZA)
    (hXB : Dichotomic XB) (hZB : Dichotomic ZB)
    (hmatch : alice ZA psi = bob ZB psi)
    (htransfer : transferError theta XA ZA XB ZB psi = 0) :
    Isometry (swapLocal XA ZA) ∧ Isometry (swapLocal XB ZB) ∧
    ‖projectionWitness theta ZA psi‖ = 1 ∧
    mapHilbertFactors (swapLocal XA ZA) (swapLocal XB ZB) psi =
      attachSchmidt (qubitCoefficients theta) (projectionWitness theta ZA psi) := by sorry

end ExtractionStatements

end QAlgorithms.Papers.Independent.Intakethird100.P75

end
