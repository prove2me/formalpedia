-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_real_complex_diagonal_forms
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.real_complex_diagonal_forms
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:06:51.173361+00:00
-- url     : https://prove2.me/theorems/4b8489d1-f166-400f-8967-cfbe20b341eb
-- title:
--   §IX (9.4a,b): real and complex diagonal forms
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$.
--
--   $$
--   V\text{ diagonal}\iff V_1,V_3\text{ diagonal},V_2=0\iff A,B\text{ real diagonal};\qquad V^{(c)}\text{ diagonal}\iff A\text{ real diagonal},B=0.
--   $$
--
--   Diagonal complex covariance implies diagonal real covariance; the converse fails even for a physical matrix. In Williamson form complex and real covariance coincide and are diagonal. Every positive definite covariance also admits a diagonal complex form under the corresponding complex symplectic congruence.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 31, §IX (9.4a,b): real and complex diagonal forms

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.31, (9.4a,b): the asymmetric diagonal-form implications,
including a physical matrix witnessing failure of the converse. -/
theorem real_complex_diagonal_forms (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsSymm) :
    (IsDiagonal V ↔ IsDiagonal (V.submatrix Sum.inl Sum.inl) ∧
      IsDiagonal (V.submatrix Sum.inr Sum.inr) ∧ V.submatrix Sum.inl Sum.inr = 0) ∧
    (IsDiagonal V ↔ IsRealDiagonal (noiseA V) ∧ IsRealDiagonal (noiseB V)) ∧
    (IsDiagonal (complexForm V) ↔ IsRealDiagonal (noiseA V) ∧ noiseB V = 0) ∧
    (IsDiagonal (complexForm V) → IsDiagonal V) ∧
    (∃ W : Matrix (Phase n) (Phase n) ℝ, Allowed W ∧ IsDiagonal W ∧
      ¬ IsDiagonal (complexForm W)) ∧
    (∀ kappa : Fin n → ℝ, complexForm (thermalCovariance kappa) = complexify (thermalCovariance kappa)) ∧
    (V.PosDef → ∃ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S ∧
      IsDiagonal (complexForm S * complexForm V * (complexForm S).conjTranspose)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
