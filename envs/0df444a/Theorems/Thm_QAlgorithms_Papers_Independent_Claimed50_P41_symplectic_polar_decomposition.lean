-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_polar_decomposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_polar_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:01:54.909003+00:00
-- url     : https://prove2.me/theorems/1b7057b6-c9d0-499d-8d40-4bc6d96d7903
-- title:
--   §IV (4.18)–(4.19): polar decomposition
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $S\in\mathrm{Sp}$.
--
--   $$
--   \exists! (K_0,P)\in K\times\Pi,\quad S=K_0P.
--   $$
--
--   There is also a unique reversed-order factorization S=Pprime Kprime with Pprime positive symplectic and Kprime passive. Uniqueness is of the ordered matrix factors; Pi is a subset, not a subgroup.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 15, §IV (4.18)–(4.19): polar decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.15, (4.18)–(4.19): unique ordered matrix factors K P. -/
theorem symplectic_polar_decomposition (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    (∃! factors : Matrix (Phase n) (Phase n) ℝ × Matrix (Phase n) (Phase n) ℝ,
      IsPassive factors.1 ∧ IsPositiveSymplectic factors.2 ∧ S = factors.1 * factors.2) ∧
    (∃! factors : Matrix (Phase n) (Phase n) ℝ × Matrix (Phase n) (Phase n) ℝ,
      IsPositiveSymplectic factors.1 ∧ IsPassive factors.2 ∧ S = factors.1 * factors.2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
