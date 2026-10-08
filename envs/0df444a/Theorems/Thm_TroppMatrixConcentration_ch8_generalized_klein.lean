-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_generalized_klein
-- name    : TroppMatrixConcentration.ch8_generalized_klein
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:51:25.88017+00:00
-- url     : https://prove2.me/theorems/de5ef9b6-c362-4322-adbf-410164eaa026
-- title:
--   Proposition 8.3.5 — Generalized Klein inequality
-- statement:
--   Let $I$ be an interval of the real line, and let $f_i,g_i:I\to\mathbb R$ be a finite family of scalar functions such that $\sum_i f_i(a)g_i(h)\ge0$ for every $a,h\in I$. If $A,H$ are Hermitian complex matrices of the same positive dimension with all eigenvalues in $I$, then
--   $$\sum_i\operatorname{Re}\operatorname{tr}[f_i(A)g_i(H)]\ge0.$$
--   No scalar continuity assumption is required, because the matrix functional calculus evaluates each function on a finite spectrum. This transfers scalar inequalities involving two variables to trace inequalities.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.3.5, printed p. 126.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_generalized_klein {d N : ℕ} [NeZero d]
    (I : Set ℝ) (hI : Convex ℝ I) (f g : Fin N → ℝ → ℝ)
    (hfg : ∀ a ∈ I, ∀ h ∈ I, 0 ≤ ∑ i, f i a * g i h)
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hHI : spectrum ℝ H ⊆ I) :
    0 ≤ ∑ i, (Matrix.trace (ch8_matrixFunction (f i) A *
      ch8_matrixFunction (g i) H)).re := by sorry

end TroppMatrixConcentration
