-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_finalStep_rowSurjectivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.finalStep_rowSurjectivity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-30T12:51:31.302524+00:00
-- url     : https://prove2.me/theorems/92357d59-48b9-4bad-b25f-4e4c68ac0f93
-- title:
--   Final-step universality is equivalent to first-row surjectivity
-- statement:
--   Let $P$ be any parameter set and let $A_p$ be a real $2\times2$ matrix of determinant one for each $p\in P$. Put $M(t)=\begin{pmatrix}-t&-1\\1&0\end{pmatrix}$. Then
--
--   $$
--   \{M(t)A_p:p\in P,\ t\in\mathbb R\}=\operatorname{Sp}(2,\mathbb R)
--   \quad\Longleftrightarrow\quad
--   \{((A_p)_{11},(A_p)_{12}):p\in P\}=\mathbb R^2\setminus\{(0,0)\}.
--   $$
--
--   The last elementary gate has an independent unrestricted real parameter. This criterion applies to any symplectic prefix family, including the teleportation prefix in §V. As on p.4, only the homogeneous Heisenberg action is represented; phase-space displacements are applied separately.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 4, §III, Lemma; Eq.(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF p.4, unnumbered Lemma and Eq.(4): universality after one unrestricted
final elementary step iff the prefix first row covers every nonzero pair.
The prefix parameter type is arbitrary, including empty. -/
theorem finalStep_rowSurjectivity
    {P : Type*} (prefixFamily : P → Mat2)
    (hPrefix : ∀ p, IsOneModeSymplectic (prefixFamily p)) :
    (∀ A : Mat2, IsOneModeSymplectic A →
      ∃ p : P, ∃ kappa : ℝ, elementary kappa * prefixFamily p = A) ↔
    (∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      ∃ p : P, prefixFamily p 0 0 = a ∧ prefixFamily p 0 1 = b) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
