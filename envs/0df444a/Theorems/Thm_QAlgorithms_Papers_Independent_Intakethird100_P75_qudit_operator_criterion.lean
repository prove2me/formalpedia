-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P75_qudit_operator_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P75.qudit_operator_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:05:45.572967+00:00
-- url     : https://prove2.me/theorems/9af56e8c-743e-4b80-a794-378d334efe26
-- title:
--   Higher-dimensional operator criterion and its extraction circuit
-- statement:
--   Let \(d\geq2\) and let \(|\psi'\rangle\) be a unit vector in the completed tensor product of arbitrary complex Hilbert spaces \(H_A,H_B\). For each party \(D=A,B\), let \(P_D(i)\), \(0\leq i<d\), be complete pairwise orthogonal self-adjoint projections and let \(X_D(i)\) be unitaries with \(X_D(0)=I\). For \(i\geq1\), let \(\delta_i\in\mathbb R\) satisfy \(\cos\delta_i\ne0\), and set \(t_0=1,t_i=\tan\delta_i\). Suppose
--   \[
--   P_A(i)|\psi'\rangle=P_B(i)|\psi'\rangle\quad(0\leq i<d),
--   \qquad
--   X_A(i)P_B(i)|\psi'\rangle=t_iX_B(i)^\dagger P_A(0)|\psi'\rangle
--   \quad(1\leq i<d).
--   \]
--   Define the initialized Figure 2 circuit maps and target by
--   \[
--   V_Dv=\sum_{i=0}^{d-1}X_D(i)P_D(i)v\otimes|i\rangle,\qquad
--   N=\sqrt{1+\sum_{i=1}^{d-1}t_i^2},\qquad
--   |\psi_t\rangle=\frac{|00\rangle+\sum_{i=1}^{d-1}t_i|ii\rangle}{N}.
--   \]
--   Then \(N>0\), the target has norm one, both \(V_D\) are complex-linear isometric embeddings, and some normalized, possibly entangled junk satisfies, after fixed register regrouping,
--   \[
--   (V_A\otimes V_B)|\psi'\rangle=|\mathrm{junk}\rangle\otimes|\psi_t\rangle.
--   \]
--   This is an exact operator criterion. Negative and zero finite ratios are allowed; all non-base ratios zero give a product target, while all ratios one give the maximally entangled target of dimension \(d\).
--
--   **Formalization Note** The circuit uses \(\omega=e^{2\pi i/d}\), \(F|j\rangle=d^{-1/2}\sum_k\omega^{jk}|k\rangle\), controlled \(Z^k\) with \(Z=\sum_i\omega^iP(i)\), inverse \(F\), and controlled \(X(i)\). Its initialized action is the displayed map. Equation (38) prints a denominator lacking squared ratios; the draft restores them, as orthonormality forces.
-- source:
--   Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States, arXiv:1210.4409v2, PDF p. 10, §IV (6); Supplement §4a, (33)–(39): higher-dimensional sufficient conditions

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

/-- PDF p.3, (6), pp.9–10, (33)–(39): higher-dimensional operator criterion.
The fixed Fig.2 action includes identity zeroth rotations. The printed (38)
normalization is corrected by squaring ratios, as orthogonality forces.
Negative and zero finite ratios are allowed; zero non-base ratios give a
product target. No correlation-certification or robust conclusion is added. -/
theorem qudit_operator_criterion (d : ℕ) (hd : 2 ≤ d)
    (delta : Fin d → ℝ)
    (hfinite : ∀ i : Fin d, i.val ≠ 0 → Real.cos (delta i) ≠ 0)
    (psi : HilbertTensor H K) (hpsi : ‖psi‖ = 1)
    (PA XA : Fin d → H →L[ℂ] H) (PB XB : Fin d → K →L[ℂ] K)
    (hPA : ProjectiveFamily PA) (hPB : ProjectiveFamily PB)
    (hXA : ∀ i, IsLocalHilbertUnitary (XA i)) (hXB : ∀ i, IsLocalHilbertUnitary (XB i))
    (hXA0 : ∀ i : Fin d, i.val = 0 → XA i = 1)
    (hXB0 : ∀ i : Fin d, i.val = 0 → XB i = 1)
    (hmatch : ∀ i, alice (PA i) psi = bob (PB i) psi)
    (htransfer : ∀ i : Fin d, i.val ≠ 0 →
      alice (XA i) (bob (PB i) psi) = (Real.tan (delta i) : ℂ) •
        bob ((XB i).adjoint) (alice (PA ⟨0, by omega⟩) psi)) :
    0 < Real.sqrt (∑ i, quditRatio delta i ^ 2) ∧
    ‖schmidtTarget (quditCoefficients delta)‖ = 1 ∧
    Isometry (quditLocal PA XA) ∧ Isometry (quditLocal PB XB) ∧
    ∃ junk : HilbertTensor H K, ‖junk‖ = 1 ∧
      mapHilbertFactors (quditLocal PA XA) (quditLocal PB XB) psi =
        attachSchmidt (quditCoefficients delta) junk := by sorry

end ExtractionStatements

end QAlgorithms.Papers.Independent.Intakethird100.P75

end
