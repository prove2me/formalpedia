-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_williamson_normal_form
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.williamson_normal_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:06:11.731522+00:00
-- url     : https://prove2.me/theorems/4aca4f59-d3c5-4533-b305-44a7c1238e9a
-- title:
--   §IX (9.1): Williamson normal form
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let V be any real symmetric positive definite matrix.
--
--   $$
--   \exists S\in\mathrm{Sp},\ \kappa_1\le\cdots\le\kappa_n,\ \kappa_r>0:\quad SVS^T=\operatorname{diag}(\kappa,\kappa).
--   $$
--
--   The same S sends -V to the negative of this diagonal, covering negative definite matrices by sign change. The parameters are Williamson eigenvalues, not ordinary Euclidean eigenvalues.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 30, §IX (9.1): Williamson normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.30, (9.1): Williamson congruence for every symmetric positive
definite real matrix, with positive sorted parameters. -/
theorem williamson_normal_form (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.PosDef) :
    ∃ kappa : Fin n → ℝ, ∃ S : Matrix (Phase n) (Phase n) ℝ,
      (∀ i, 0 < kappa i) ∧ Monotone kappa ∧ PreservesCanonicalForm S ∧
      S * V * S.transpose = thermalCovariance kappa ∧
      S * (-V) * S.transpose = -thermalCovariance kappa := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
