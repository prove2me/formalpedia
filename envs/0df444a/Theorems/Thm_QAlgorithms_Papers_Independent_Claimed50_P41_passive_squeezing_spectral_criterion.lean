-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_passive_squeezing_spectral_criterion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.passive_squeezing_spectral_criterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:08:02.634998+00:00
-- url     : https://prove2.me/theorems/8895e194-728a-4ec0-a895-faa08fdf1bb5
-- title:
--   §X (10.5) iff (10.6): invariant squeezing criterion
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. Let V belong to S and let l(V) denote its least ordinary eigenvalue.
--
--   $$
--   \bigl(\exists K_0\in K,\ \exists a,\ (K_0VK_0^T)_{aa}<\tfrac12\bigr)\iff l(V)<\tfrac12.
--   $$
--
--   The left side is the source passive-invariant definition of squeezing. It is unchanged by every passive transformation. The eigenvalue is Euclidean, rather than a Williamson symplectic eigenvalue.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 33, §X (10.5) iff (10.6): invariant squeezing criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.32–33, (10.5) iff (10.6): passive squeezing iff minimum
ordinary eigenvalue <1/2, with passive invariance. -/
theorem passive_squeezing_spectral_criterion (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : Allowed V) :
    (PassiveSqueezing V ↔ minimumEigenvalue hn V hV.1.isHermitian < 1 / 2) ∧
    (∀ K : Matrix (Phase n) (Phase n) ℝ, IsPassive K →
      (PassiveSqueezing (K * V * K.transpose) ↔ PassiveSqueezing V)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
