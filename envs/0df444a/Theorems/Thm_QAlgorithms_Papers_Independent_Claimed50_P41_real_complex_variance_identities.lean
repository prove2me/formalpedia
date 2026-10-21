-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_real_complex_variance_identities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.real_complex_variance_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:05:48.39866+00:00
-- url     : https://prove2.me/theorems/ca2bdcd1-3448-4d52-b128-b1c492ebba84
-- title:
--   §VIII (8.5)–(8.6): real/complex variance identities
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. Write $V=\begin{pmatrix}V_1&V_2\\V_2^T&V_3\end{pmatrix}$ with V1 and V3 symmetric.
--
--   $$
--   A=\tfrac12(V_1+V_3+i(V_2^T-V_2)),\qquad B=\tfrac12(V_1-V_3+i(V_2^T+V_2)).
--   $$
--
--   The theorem gives the full block form, A Hermitian, B symmetric, and all three inverse equations in (8.6): V1=(A+conjugate A+B+conjugate B)/2, V2=i(A-conjugate A-B+conjugate B)/2, V3=(A+conjugate A-B-conjugate B)/2. Positive definite V gives positive definite complex covariance. These algebraic identities apply to every real symmetric V; the arbitrary-density moment construction is deferred separately.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 29, §VIII (8.5)–(8.6): real/complex variance identities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.29, (8.5)–(8.6): the complete real/complex matrix identities.
The operator-moment construction is handled separately; these identities apply
to every real symmetric matrix, as the source's formulas themselves do. -/
theorem real_complex_variance_identities (n : ℕ) (hn : 0 < n)
    (Vone Vtwo Vthree : Matrix (Fin n) (Fin n) ℝ)
    (hVone : Vone.IsSymm) (hVthree : Vthree.IsSymm) :
    let V := Matrix.fromBlocks Vone Vtwo Vtwo.transpose Vthree
    let A := noiseA V
    let B := noiseB V
    A.IsHermitian ∧ B.IsSymm ∧
    complexForm V = Matrix.fromBlocks A B (fun i j => star (B i j)) (fun i j => star (A i j)) ∧
    A = (1 / 2 : ℂ) • (complexify Vone + complexify Vthree +
      Complex.I • (complexify Vtwo.transpose - complexify Vtwo)) ∧
    B = (1 / 2 : ℂ) • (complexify Vone - complexify Vthree +
      Complex.I • (complexify Vtwo.transpose + complexify Vtwo)) ∧
    complexify Vone = (1 / 2 : ℂ) •
      (A + A.map star + B + B.map star) ∧
    complexify Vtwo = (Complex.I / 2) •
      (A - A.map star - B + B.map star) ∧
    complexify Vthree = (1 / 2 : ℂ) •
      (A + A.map star - B - B.map star) ∧
    (V.PosDef → (complexForm V).PosDef) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
