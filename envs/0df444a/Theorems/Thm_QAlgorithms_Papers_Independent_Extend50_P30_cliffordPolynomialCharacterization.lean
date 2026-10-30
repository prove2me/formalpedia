-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cliffordPolynomialCharacterization
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cliffordPolynomialCharacterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:34:23.172172+00:00
-- url     : https://prove2.me/theorems/3d0c90f0-eeea-4958-8ef1-a12bacc0f79e
-- title:
--   Degree-six polynomial characterization of Clifford unitaries
-- statement:
--   For each $n$, form the coordinate polynomials obtained by applying the six-copy anti-identity to six tensor copies of the unnormalized Choi vector and subtracting that vector. The variables are the complex entries of an $n$-qubit matrix $U$. Each polynomial has total degree at most six. Among unitary matrices, their common zero set is exactly the Clifford normalizer; unitarity remains an essential domain restriction.
--
--   $$
--   \deg P_x\leq6,\qquad U\in\mathrm{Cliff}(n,2)\iff P_x(U)=0\ \text{for every coordinate }x\quad(U\in U(2^n)).
--   $$
--
--   This gives the source's degree-six polynomial characterization of clifford unitaries in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 8, clifford-polynomial-characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.8: concrete homogeneous degree-six equations characterize Clifford unitaries within U(2^n). -/
theorem cliffordPolynomialCharacterization (n : ℕ) :
    (∀ x : QuditCopies 2 (n + n) 6, (cliffordPolynomial n x).totalDegree ≤ 6) ∧
    (∀ U : QuditOperator 2 n, U ∈ Matrix.unitaryGroup (ResidueRegister 2 n) ℂ →
      (IsClifford U ↔ ∀ x : QuditCopies 2 (n + n) 6,
        MvPolynomial.eval (fun a => U a.1 a.2) (cliffordPolynomial n x) = 0)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
