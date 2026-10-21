-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_manifest_implies_invariant_squeezing
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.manifest_implies_invariant_squeezing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:07:38.047903+00:00
-- url     : https://prove2.me/theorems/69325c05-010c-4800-ae5b-459eaeb96d45
-- title:
--   §X (10.4): manifest squeezing implies invariant squeezing
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. In one mode write l(V) for the least ordinary eigenvalue of V.
--
--   $$
--   \Delta q<1/\sqrt2\ \text{or}\ \Delta p<1/\sqrt2\quad\Longrightarrow\quad l(V)<\tfrac12.
--   $$
--
--   This holds for every matrix in the source family S. There exists a member of S with l(V)<1/2 and both diagonal variances at least 1/2, so the converse fails in fixed axes. Passive rotations preserve the least ordinary eigenvalue.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 32, §X (10.4): manifest squeezing implies invariant squeezing

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.32, (10.4): manifest standard-deviation squeezing implies
ordinary-eigenvalue squeezing, and the converse fails even for physical one-mode matrices. -/
theorem manifest_implies_invariant_squeezing :
    (∀ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V),
      (Real.sqrt (V (Sum.inl 0) (Sum.inl 0)) < (Real.sqrt 2)⁻¹ ∨
       Real.sqrt (V (Sum.inr 0) (Sum.inr 0)) < (Real.sqrt 2)⁻¹) →
      minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian < 1 / 2) ∧
    (∃ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V),
      minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian < 1 / 2 ∧
        ¬ ManifestSqueezing V) ∧
    (∀ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V)
      (K : Matrix (Phase 1) (Phase 1) ℝ), IsPassive K →
      ∃ hW : (K * V * K.transpose).IsHermitian,
        minimumEigenvalue (by decide : 0 < 1) (K * V * K.transpose) hW =
          minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
