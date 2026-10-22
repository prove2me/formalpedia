-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_one_mode_uncertainty
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.one_mode_uncertainty
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:07:15.084765+00:00
-- url     : https://prove2.me/theorems/8beeb451-3db0-470c-b57b-5f303f161386
-- title:
--   §X (10.2)–(10.3): one-mode uncertainty
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. In one mode let V belong to the source matrix family S, and put $\Delta q=\sqrt{V_{qq}}$, $\Delta p=\sqrt{V_{pp}}$, $c=V_{qp}$.
--
--   $$
--   \Delta q\,\Delta p\ge\tfrac12,\qquad\det V=V_{qq}V_{pp}-c^2\ge\tfrac14.
--   $$
--
--   For a real symmetric one-mode matrix the uncertainty criterion is equivalent to Vqq positive and determinant at least one quarter. The determinant is invariant under symplectic congruence. This is the matrix uncertainty statement on the source family (11.1); arbitrary-state moment realizability is a distinct deferred result.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 32, §X (10.2)–(10.3): one-mode uncertainty

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.31–32, (10.2)–(10.3): one-mode uncertainty for matrices in
the source family S (11.1); deltas are square roots of variances. -/
theorem one_mode_uncertainty (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V) :
    Real.sqrt (V (Sum.inl 0) (Sum.inl 0)) * Real.sqrt (V (Sum.inr 0) (Sum.inr 0)) ≥ 1 / 2 ∧
    V.det = V (Sum.inl 0) (Sum.inl 0) * V (Sum.inr 0) (Sum.inr 0) -
      V (Sum.inl 0) (Sum.inr 0) ^ 2 ∧ V.det ≥ 1 / 4 ∧
    (∀ W : Matrix (Phase 1) (Phase 1) ℝ, W.IsSymm →
      (Allowed W ↔ 0 < W (Sum.inl 0) (Sum.inl 0) ∧ 1 / 4 ≤ W.det)) ∧
    (∀ S : Matrix (Phase 1) (Phase 1) ℝ, PreservesCanonicalForm S → (S * V * S.transpose).det = V.det) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
