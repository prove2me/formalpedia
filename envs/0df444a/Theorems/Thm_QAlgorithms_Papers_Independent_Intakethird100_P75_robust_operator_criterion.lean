-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P75_robust_operator_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P75.robust_operator_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:04:37.501609+00:00
-- url     : https://prove2.me/theorems/9abc1432-3492-4999-9db5-4643622dec14
-- title:
--   Approximate operator identities imply robust extraction
-- statement:
--   Let \(|\psi'\rangle\) be a unit vector in the completed tensor product of arbitrary complex Hilbert spaces \(H_A,H_B\), and let \(X_A,Z_A,X_B,Z_B\) be local bounded self-adjoint involutions. Choose \(0\leq\theta\leq\pi/4\) and nonnegative tolerances \(\epsilon,\tau\), and suppose
--   \[
--   \|(Z_A-Z_B)|\psi'\rangle\|\leq2\epsilon,\qquad
--   \|(\sin\theta\,X_A(I+Z_B)-\cos\theta\,X_B(I-Z_A))|\psi'\rangle\|\leq\tau.
--   \]
--   Put
--   \[
--   \bar\epsilon=4\epsilon+\frac{\tau}{2|\cos\theta|}<1,\qquad
--   |q\rangle=\frac{I+Z_A}{2\cos\theta}|\psi'\rangle,\qquad
--   |\mathrm{junk}\rangle=\frac{|q\rangle}{\|q\|}.
--   \]
--   Then \(q\ne0\), junk is normalized, and the fixed complex-linear maps
--   \[
--   V_Dv=\frac{(I+Z_D)v\otimes|0\rangle+X_D(I-Z_D)v\otimes|1\rangle}{2}
--   \quad(D=A,B)
--   \]
--   are isometric embeddings satisfying, after fixed register regrouping,
--   \[
--   \|(V_A\otimes V_B)|\psi'\rangle-
--   |\mathrm{junk}\rangle\otimes(\cos\theta|00\rangle+\sin\theta|11\rangle)\|
--   \leq2\bar\epsilon.
--   \]
--   This isolates the conditional extraction argument (24)–(32). The tolerance \(\tau\), denoted \(\epsilon'_2\) in the paper, is an independent input. The small-error condition permits normalization of the specified witness; no invalid Bell-deficit conversion is assumed.
-- source:
--   Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States, arXiv:1210.4409v2, PDF p. 8, Supplement §3b, (24)–(32): robust extraction from approximate operator identities

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

/-- PDF pp.8–9, (24)–(32): conditional robust extraction. epsilon2 is an
independent tolerance, not an assumed consequence of a Bell deficit. The
small-error regime makes the specified projection witness nonzero before
normalization. The full factor 2 of (32) is retained. -/
theorem robust_operator_criterion (theta epsilon epsilon2 : ℝ)
    (htheta : 0 ≤ theta) (hthetaUpper : theta ≤ Real.pi / 4)
    (hepsilon : 0 ≤ epsilon) (hepsilon2 : 0 ≤ epsilon2)
    (hsmall : extractionBudget theta epsilon epsilon2 < 1)
    (psi : HilbertTensor H K) (hpsi : ‖psi‖ = 1)
    (XA ZA : H →L[ℂ] H) (XB ZB : K →L[ℂ] K)
    (hXA : Dichotomic XA) (hZA : Dichotomic ZA)
    (hXB : Dichotomic XB) (hZB : Dichotomic ZB)
    (hmatch : ‖alice ZA psi - bob ZB psi‖ ≤ 2 * epsilon)
    (htransfer : ‖transferError theta XA ZA XB ZB psi‖ ≤ epsilon2) :
    Isometry (swapLocal XA ZA) ∧ Isometry (swapLocal XB ZB) ∧
    projectionWitness theta ZA psi ≠ 0 ∧
    ‖normalizedProjection theta ZA psi‖ = 1 ∧
    ‖mapHilbertFactors (swapLocal XA ZA) (swapLocal XB ZB) psi -
      attachSchmidt (qubitCoefficients theta) (normalizedProjection theta ZA psi)‖ ≤
        2 * extractionBudget theta epsilon epsilon2 := by sorry

end ExtractionStatements

end QAlgorithms.Papers.Independent.Intakethird100.P75

end
