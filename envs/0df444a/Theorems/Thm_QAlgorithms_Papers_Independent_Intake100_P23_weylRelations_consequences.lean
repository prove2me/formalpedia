-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_weylRelations_consequences
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.weylRelations_consequences
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:39:34.969304+00:00
-- url     : https://prove2.me/theorems/1349cb92-52e1-4c32-98c9-bce44ab6189b
-- title:
--   Consequences of the Weyl relations
-- statement:
--   Let $Y$ be a real vector space with antisymmetric real bilinear form $\omega$, possibly degenerate. Let $W:Y\to\mathcal U(H)$ be a Weyl representation on any complex Hilbert space, so $W(y)W(z)=e^{-i\omega(y,z)/2}W(y+z)$. Then
--   $$\begin{gathered}W(y)W(z)=e^{-i\omega(y,z)}W(z)W(y),\\W(y)^*=W(-y),\quad W(0)=1,\\W(sy)W(ty)=W((s+t)y)\quad(s,t\in\mathbb R).\end{gathered}$$
--   These identities supply inverses and the one-parameter groups underlying field operators.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 9, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.9, Theorem 2: all of (10), (11), and (12). -/
theorem weylRelations_consequences (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hanti : Antisymmetric omega) (W : Y → H →L[ℂ] H) (hW : IsCCR omega W) :
    (∀ y z, W y * W z = Complex.exp (-Complex.I * (omega y z : ℂ)) • (W z * W y)) ∧
    (∀ y, star (W y) = W (-y)) ∧ W 0 = 1 ∧
    (∀ (y : Y) (s t : ℝ), W (s • y) * W (t • y) = W ((s + t) • y)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P23

end
