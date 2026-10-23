-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_special_variance_families
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.special_variance_families
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:09:16.132199+00:00
-- url     : https://prove2.me/theorems/f88fa889-3ec1-46f6-8122-48ee195c794e
-- title:
--   §XI (11.4)–(11.6): special families and squeezing
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. Use the families SK, SH and SG defined in the preceding target, and let squeezing mean existence of a passive transform exposing a diagonal variance below 1/2. Here $\mathcal S_K=\{V\in\mathcal S:AB=(AB)^T\}$, $\mathcal S_H=\{V\in\mathcal S_K:B=0,\ A-I/2\succeq0\}$ and $\mathcal S_G=\{V\in\mathcal S_K:2V\in\Pi\}$.
--
--   $$
--   \mathcal S_H,\mathcal S_G\subseteq\mathcal S_K\subseteq\mathcal S,\quad\mathcal S_H\cap\mathcal S_G=\{I/2\}.
--   $$
--
--   Every positive symplectic P gives P/2 in SG, hence an admissible and passively diagonalizable matrix as a conclusion. No member of SH is squeezed. Every member of SG except I/2 is squeezed. Realizability by an actual density operator is the separate uncertainty-interface node, not defined by these matrix tuples.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 34, §XI (11.4)–(11.6): special families and squeezing

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.34, (11.4)–(11.6): inclusions, physicality and passive
diagonalizability of every positive symplectic half-matrix, squeezing except
at vacuum, and the unique intersection SH cap SG={I/2}. -/
theorem special_variance_families (n : ℕ) (hn : 0 < n) :
    familyH n ⊆ familyK n ∧ familyG n ⊆ familyK n ∧
    familyK n ⊆ {V | Allowed V} ∧
    (∀ P : Matrix (Phase n) (Phase n) ℝ, IsPositiveSymplectic P →
      (1 / 2 : ℝ) • P ∈ familyG n) ∧
    (∀ V ∈ familyH n, ¬ PassiveSqueezing V) ∧
    (∀ V ∈ familyG n, V ≠ (1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ) →
      PassiveSqueezing V) ∧
    familyH n ∩ familyG n = {(1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ)} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
