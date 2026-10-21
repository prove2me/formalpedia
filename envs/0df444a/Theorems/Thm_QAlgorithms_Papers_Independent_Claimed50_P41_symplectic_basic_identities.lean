-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_basic_identities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_basic_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:58:30.313449+00:00
-- url     : https://prove2.me/theorems/4882a55e-2305-4eb7-a1aa-1420acbe1d55
-- title:
--   §IV (4.1)(ii)–(iv): elementary group identities
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $S\in\mathrm{Sp}$.
--
--   $$
--   \beta,-S,S^{-1},S^T\in\mathrm{Sp},\quad S^T=\beta S^{-1}\beta^{-1},\quad S^{-T}=\beta S\beta^{-1},\quad S^{-1}=\beta S^T\beta^{-1},\quad\det S=1.
--   $$
--
--   These are the grouped elementary group identities of the source, including determinant plus one.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 11, §IV (4.1)(ii)–(iv): elementary group identities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.11, (4.1)(ii)–(iv): group identities and determinant +1. -/
theorem symplectic_basic_identities (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    PreservesCanonicalForm (sigma n) ∧ PreservesCanonicalForm (-S) ∧ PreservesCanonicalForm S⁻¹ ∧
    PreservesCanonicalForm S.transpose ∧
    S.transpose = sigma n * S⁻¹ * (sigma n)⁻¹ ∧
    S⁻¹.transpose = sigma n * S * (sigma n)⁻¹ ∧
    S⁻¹ = sigma n * S.transpose * (sigma n)⁻¹ ∧ S.det = 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
