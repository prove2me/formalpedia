-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_ball_positive_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.ball_positive_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:29:23.537733+00:00
-- url     : https://prove2.me/theorems/1ce6d0ed-6637-44a7-93ff-807f3d9201d0
-- title:
--   Ball power kernel: exact positivity range
-- statement:
--   Let \(n\ge1\) be an integer, \(s\in\mathbb R\), and \(D=\{x\in\mathbb R^n:\|x\|<1\}\). Define the kernel directly in ball coordinates by
--   \[
--   R_s(x,y)=\bigl(1-2\langle x,y\rangle+\|x\|^2\|y\|^2\bigr)^{-s/2}.
--   \]
--   Then \(R_s\) is positive definite on \(D\) if and only if
--   \[
--   s=0\quad\text{or}\quad s\ge\max\{0,n-2\}.
--   \]
--   The inner product here is the real Euclidean one. The base of the power is strictly positive on the open ball, including when either point is zero.
--
--   This gives the ball version of the sharp reflection-positivity parameter range, without introducing a totalized inversion at the center or an upper bound on \(s\).
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 36, Proposition 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Proposition 6.2, PDF pp. 36-37: exact parameter classification, including n=1,2
and s=0. The real subtraction n-2 is not truncated natural subtraction. -/
theorem ball_positive_iff (n : ℕ) (hn : 0 < n) (s : ℝ) :
    PositiveKernel (ballKernel n s) ↔
      s = 0 ∨ max (0 : ℝ) ((n : ℝ) - 2) ≤ s := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
