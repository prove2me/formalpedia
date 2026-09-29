-- Prove2me | Theorems.Thm_Rosenblatt_exists_finiteIndex_isUpperTriangular_of_isSolvable
-- name    : Rosenblatt.exists_finiteIndex_isUpperTriangular_of_isSolvable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-09-21T16:55:53.818794+00:00
-- url     : https://prove2.me/theorems/b9edc514-0b7d-44ff-9112-07388e9bfde3
-- title:
--   Lemma 4.18 (Mal'cev): a solvable group of real matrices has a finite-index subgroup that can be simultaneously triangularized over the complex numbers
-- statement:
--   Let $S$ be a subgroup of the group of invertible $n \times n$ real matrices, and
--   suppose $S$ is **solvable** as an abstract group. Then there is a subgroup $H \le S$ of finite
--   index and a single invertible complex matrix $P$ such that for every $M \in H$, conjugating the
--   entrywise complexification of $M$ by $P$ gives an upper-triangular matrix:
--   $$P^{-1}\,\widehat{M}\,P \quad\text{is upper triangular for all } M \in H,$$
--   where $\widehat{M}$ is $M$ with each real entry $r$ read as $r + 0i$.
--
--   *Reading the pieces.* "Upper triangular" is `Matrix.IsUpperTriangular`, which says the
--   **strictly lower** triangle vanishes — the diagonal is unconstrained. $P$ is bound outside the
--   quantifier over $M$, so one $P$ triangularizes all of $H$ **simultaneously**; that is the whole
--   force of the statement. "Finite index" means finitely many left cosets of $H$ **inside $S$**,
--   not inside the full matrix group, and no bound on the index is claimed. The matrix inverse is
--   Mathlib's total nonsingular inverse, which returns $0$ when the determinant is not invertible;
--   the hypothesis that $P$ is a unit is what makes $P^{-1}$ a genuine two-sided inverse, and it is
--   essential rather than decorative — without it one could take $P$ singular, making
--   $P^{-1}\widehat{M}P = 0$, which is upper triangular for free.
--
--   *What is not claimed.* $H$ is not asserted to be normal in $S$; nothing is claimed about the
--   diagonal entries of the triangularized matrices; $P$ is not claimed to be real or unitary; and
--   no converse is asserted.
--
--   *Degenerate ranges, stated because they are real.* For $n = 0$ and $n = 1$ no index pair lies
--   strictly below the diagonal, so every matrix is upper triangular and the conclusion holds for
--   any $S$ whatever, with $H = S$ and $P = I$ — at $n \le 1$ the statement has no content. If $S$
--   is finite the conclusion also holds for free, taking $H$ trivial, which has finite index in a
--   finite group. And if $S$ already consists of upper-triangular matrices one may take $H = S$ and
--   $P = I$. The substance of the theorem is confined to $n \ge 2$ with $S$ infinite, where the
--   finite-index clause is exactly the weakening that makes it true: a solvable linear group need
--   not itself be triangularizable.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Lemma 4.18, p. 48, where it is quoted without proof from A. I. Mal'cev, On certain classes of infinite solvable groups, Mat. Sb. 28 (70) (1951) 567-588; English translation, Amer. Math. Soc. Transl. (2) 2 (1956) 1-21

import Mathlib

namespace Rosenblatt

theorem exists_finiteIndex_isUpperTriangular_of_isSolvable {n : ℕ}
    (S : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℝ)) [Group.IsSolvable S] :
    ∃ (H : Subgroup S) (P : Matrix (Fin n) (Fin n) ℂ), H.FiniteIndex ∧ IsUnit P ∧
      ∀ M ∈ H, (P⁻¹ * (((M : Matrix.GeneralLinearGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal) * P).IsUpperTriangular := by
  sorry

end Rosenblatt
