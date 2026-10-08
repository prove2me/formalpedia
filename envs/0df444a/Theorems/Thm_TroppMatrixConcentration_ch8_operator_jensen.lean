-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_operator_jensen
-- name    : TroppMatrixConcentration.ch8_operator_jensen
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:52:56.088978+00:00
-- url     : https://prove2.me/theorems/c6ba5b84-5c6c-44bc-8d4a-12ba1001a288
-- title:
--   Theorem 8.5.2 — Operator Jensen inequality
-- statement:
--   Let $f$ be operator convex on a real interval $I$. Let $A_1,A_2$ be Hermitian complex matrices with spectra in $I$, and let $K_1,K_2$ be compatible rectangular complex matrices with the same positive number of columns and
--   $$K_1^*K_1+K_2^*K_2=I.$$
--   Then
--   $$f(K_1^*A_1K_1+K_2^*A_2K_2)\preceq K_1^*f(A_1)K_1+K_2^*f(A_2)K_2.$$
--   All matrix dimensions are positive. This extends scalar convex combinations to matrix convex combinations; the two input matrices may have different compatible sizes.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 8.5.2 and Chapter 8 dimension conventions, printed pp. 120, 132–133.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_operator_jensen {d m n : ℕ} [NeZero d] [NeZero m] [NeZero n]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (A₁ : Matrix (Fin m) (Fin m) ℂ) (A₂ : Matrix (Fin n) (Fin n) ℂ)
    (hA₁ : A₁.IsHermitian) (hA₂ : A₂.IsHermitian)
    (hA₁I : spectrum ℝ A₁ ⊆ I) (hA₂I : spectrum ℝ A₂ ⊆ I)
    (K₁ : Matrix (Fin m) (Fin d) ℂ) (K₂ : Matrix (Fin n) (Fin d) ℂ)
    (hK : K₁.conjTranspose * K₁ + K₂.conjTranspose * K₂ = 1) :
    loewnerLE
      (ch8_matrixFunction f (K₁.conjTranspose * A₁ * K₁ + K₂.conjTranspose * A₂ * K₂))
      (K₁.conjTranspose * ch8_matrixFunction f A₁ * K₁ +
        K₂.conjTranspose * ch8_matrixFunction f A₂ * K₂) := by sorry

end TroppMatrixConcentration
