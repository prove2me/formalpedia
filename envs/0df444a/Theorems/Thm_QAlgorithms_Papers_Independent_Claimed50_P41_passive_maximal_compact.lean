-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_passive_maximal_compact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.passive_maximal_compact
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:00:58.501846+00:00
-- url     : https://prove2.me/theorems/d7f3824f-4fff-49a3-8b2a-505b7a376945
-- title:
--   §IV (4.9)–(4.14): maximal compact passive subgroup
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For $U=X-iY$ define $K(U)=\begin{pmatrix}X&Y\\-Y&X\end{pmatrix}$.
--
--   $$
--   K\cong U(n),\quad K=\mathrm{Sp}\cap O(2n)=\mathrm{Sp}\cap SO(2n),\quad K(U)^{(c)}=\operatorname{diag}(U,\overline U).
--   $$
--
--   The map is injective and multiplicative, and K has dimension n squared. K is a compact subgroup inclusion-maximal among compact subgroups of Sp. Within Sp, precisely these matrices have zero off-diagonal Bogoliubov blocks. The embedded GL subgroup intersects K in the embedded O subgroup.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 14, §IV (4.9)–(4.14): maximal compact passive subgroup

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.13–14, (4.9)–(4.14): K(n) is precisely the orthogonal symplectic
subgroup and the block-independent Bogoliubov subgroup, and is inclusion-maximal
among compact subgroups. Entrywise conjugation below is not adjoint. -/
theorem passive_maximal_compact (n : ℕ) (hn : 0 < n) :
    (∀ K : Matrix (Phase n) (Phase n) ℝ,
      (IsPassive K ↔ PreservesCanonicalForm K ∧ K.transpose * K = 1 ∧ K.det = 1) ∧
      (IsPassive K ↔ ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
        (unitaryParameter X Y).conjTranspose * unitaryParameter X Y = 1 ∧
          K = passiveMatrix X Y)) ∧
    (∀ X Y : Matrix (Fin n) (Fin n) ℝ,
      (unitaryParameter X Y).conjTranspose * unitaryParameter X Y = 1 →
        complexForm (passiveMatrix X Y) = Matrix.fromBlocks
          (unitaryParameter X Y) 0 0 (fun i j => star (unitaryParameter X Y i j))) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      (IsPassive S ↔ (complexForm S).submatrix Sum.inl Sum.inr = 0 ∧
        (complexForm S).submatrix Sum.inr Sum.inl = 0)) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det →
      (IsPassive (glMatrix A) ↔ A.transpose * A = 1)) ∧
    IsMatrixSubgroup {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} ∧
    IsCompact {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} ∧
    (∀ H : Set (Matrix (Phase n) (Phase n) ℝ), IsMatrixSubgroup H → IsCompact H →
      (∀ S ∈ H, PreservesCanonicalForm S) → {K | IsPassive K} ⊆ H → H = {K | IsPassive K}) ∧
    Function.Injective (fun f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      passiveMatrix f.1 f.2) ∧
    (∀ X Y Xprime Yprime : Matrix (Fin n) (Fin n) ℝ,
      passiveMatrix X Y * passiveMatrix Xprime Yprime =
        passiveMatrix (X * Xprime - Y * Yprime) (X * Yprime + Y * Xprime)) ∧
    dimH {K : Matrix (Phase n) (Phase n) ℝ | IsPassive K} = (n ^ 2 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
