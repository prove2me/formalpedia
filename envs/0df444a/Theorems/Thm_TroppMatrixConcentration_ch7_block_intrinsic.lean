-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_block_intrinsic
-- name    : TroppMatrixConcentration.ch7_block_intrinsic
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:52:12.188973+00:00
-- url     : https://prove2.me/theorems/5b9b7477-9339-48bb-b87a-b0f6c6ab98e0
-- title:
--   Equation 7.3.4 — Intrinsic dimension of variance blocks
-- statement:
--   Let $V_1,V_2$ be positive semidefinite complex square matrices of positive sizes and let $V=\operatorname{diag}(V_1,V_2)$. Then $V$ is positive semidefinite and
--   $$\|V\|=\max\{\|V_1\|,\|V_2\|\},\qquad r(V)=\frac{\operatorname{tr}V_1+\operatorname{tr}V_2}{\max\{\|V_1\|,\|V_2\|\}},$$
--   $$\min\{r(V_1),r(V_2)\}\le r(V)\le r(V_1)+r(V_2).$$
--   The result includes zero blocks under $r(0)=0$ and totalized real division. These are the intrinsic-dimension and variance relations used in the rectangular dilation reduction.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Equation (7.3.4) and preceding identity, printed p. 109; Section 7.7.3, printed p. 117.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_block_intrinsic {m n : ℕ} [NeZero m] [NeZero n]
    (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ)
    (hV₁ : V₁.PosSemidef) (hV₂ : V₂.PosSemidef) :
    let V := Matrix.fromBlocks V₁ 0 0 V₂
    V.PosSemidef ∧
    spectralNorm V = max (spectralNorm V₁) (spectralNorm V₂) ∧
    intrinsicDimension V =
      ((Matrix.trace V₁).re + (Matrix.trace V₂).re) /
        max (spectralNorm V₁) (spectralNorm V₂) ∧
    min (intrinsicDimension V₁) (intrinsicDimension V₂) ≤ intrinsicDimension V ∧
    intrinsicDimension V ≤ intrinsicDimension V₁ + intrinsicDimension V₂ := by sorry

end TroppMatrixConcentration
