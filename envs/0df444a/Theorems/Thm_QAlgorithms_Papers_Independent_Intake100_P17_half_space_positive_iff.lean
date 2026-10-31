-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_half_space_positive_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.half_space_positive_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:28:46.674054+00:00
-- url     : https://prove2.me/theorems/f404aabd-de19-4678-9fe7-41f47e8a5c65
-- title:
--   Half-space power covariance: exact positivity range
-- statement:
--   Let \(n\ge1\) be an integer and \(s\in\mathbb R\). Write \(\mathbb R^n_+=\{x:x_0>0\}\) and \(x^\sharp=(x_0,-x_1,\ldots,-x_{n-1})\). The function \(x\mapsto\|x\|^{-s}\) is positive definite on this additive involutive semigroup exactly when
--   \[
--   s=0\quad\text{or}\quad s\ge\max\{0,n-2\}.
--   \]
--   Equivalently, the scalar kernel \(K_s(x,y)=\|x+y^\sharp\|^{-s}\) is positive definite, with arbitrary finite complex coefficients, if and only if this parameter condition holds.
--
--   This is a pointwise kernel classification; it requires no local-integrability bound \(s<n\). The half-space ensures the norm in the kernel is strictly positive.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 36, Proposition 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Proposition 6.1, PDF p. 36: necessity and sufficiency hold for every real s.
In contrast with distributional local integrability, there is no assumption s < n. -/
theorem half_space_positive_iff (n : ℕ) (hn : 0 < n) (s : ℝ) :
    PositiveKernel (halfSpaceKernel n hn s) ↔
      s = 0 ∨ max (0 : ℝ) ((n : ℝ) - 2) ≤ s := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
