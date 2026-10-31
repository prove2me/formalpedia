-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P11_fourElementarySteps_necessaryAndSufficient
-- name    : QAlgorithms.Papers.Independent.Intake100.P11.fourElementarySteps_necessaryAndSufficient
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:52:08.983192+00:00
-- url     : https://prove2.me/theorems/679ae4f1-7d2e-4d14-8599-9ef9dc7e41e2
-- title:
--   Four elementary steps are necessary and sufficient uniformly over one-mode targets
-- statement:
--   For real $t$, let $M(t)=\begin{pmatrix}-t&-1\\1&0\end{pmatrix}$. For a finite chronological word $w=(t_1,\ldots,t_m)$ define $W(w)=M(t_m)\cdots M(t_1)$, with $W(\varnothing)=I$. The source construction uses one ancilla per elementary step with external input. Then
--
--   $$
--   \forall S\in\operatorname{Sp}(2,\mathbb R),\quad
--   \exists w:\ |w|=4,\quad W(w)=S,
--   $$
--
--   whereas for every $m\in\{0,1,2,3\}$ there is a determinant-one matrix $S_m$ that no word of length $m$ represents. Thus four ancilla modes suffice for the elementary chain, and four is the minimum uniform number of elementary steps.
--
--   This is universality of the homogeneous ideal action within the source chain model. It neither asserts that each target needs four steps nor supplies a lower bound for arbitrary cluster graphs.
-- source:
--   Universal linear Bogoliubov transformations through one-way quantum computation, arXiv:0910.0660v1, PDF p. 4, §III, unnumbered Theorem; proof pp.4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P11

noncomputable section

open scoped Matrix BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P11

/-- PDF pp.4--5, unnumbered Theorem: minimum uniform elementary-word length
four. The obstruction covers each length 0,1,2,3 within the FO(kappa) chain
model, not arbitrary graphs; individual targets can require fewer steps. -/
theorem fourElementarySteps_necessaryAndSufficient :
    (∀ A : Mat2, IsOneModeSymplectic A →
      ∃ settings : List ℝ, settings.length = 4 ∧
        elementaryAncillas settings = 4 ∧ elementaryWord settings = A) ∧
    (∀ m : ℕ, m < 4 → ∃ A : Mat2, IsOneModeSymplectic A ∧
      ∀ settings : List ℝ, settings.length = m → elementaryWord settings ≠ A) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P11

end
