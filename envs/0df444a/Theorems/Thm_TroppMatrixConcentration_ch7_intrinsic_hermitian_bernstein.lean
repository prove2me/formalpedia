-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_hermitian_bernstein
-- name    : TroppMatrixConcentration.ch7_intrinsic_hermitian_bernstein
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:52:55.161729+00:00
-- url     : https://prove2.me/theorems/4e3cb6ca-6d2f-4a56-8f2c-d2f0f777a81b
-- title:
--   Theorem 7.7.1 — Intrinsic Hermitian matrix Bernstein
-- statement:
--   Let $X_k$ be independent measurable Hermitian complex $d\times d$ random matrices, with finite second moments, mean zero, and $\lambda_{\max}(X_k)\le L$ almost surely, where $d\ge1$ and $L\ge0$. Write $Y=\sum_kX_k$. Let $V\ne0$ satisfy $V\succeq\mathbb EY^2$, and put $v=\|V\|$. Then
--   $$\mathbb EY^2=\sum_k\mathbb EX_k^2,$$
--   $$\mathbb P\{\lambda_{\max}(Y)\ge t\}\le4r(V)\exp\!\left(-\frac{t^2/2}{v+Lt/3}\right)\quad(t\ge\sqrt v+L/3).$$
--   The summand bound is one-sided; no lower eigenvalue or full norm bound is imposed. Finite second moments implement the source's standing integrability convention. Nonzero $V$ makes the intrinsic dimension well-defined and the displayed denominator positive.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 7.7.1, equation (7.7.1), printed p. 115; proof in Section 7.7.2, printed pp. 115–117.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_intrinsic_hermitian_bernstein {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (L : ℝ) (hL : 0 ≤ L) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ≠ 0)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ)
    (hMean : ∀ k, (∫ ω, X k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L)
    (hVarianceBound : loewnerLE (∫ ω, (∑ k, X k ω) ^ 2 ∂μ) V) :
    let Y := fun ω => ∑ k, X k ω
    let v := spectralNorm V
    (∫ ω, Y ω ^ 2 ∂μ) = ∑ k, ∫ ω, X k ω ^ 2 ∂μ ∧
    ∀ t : ℝ, Real.sqrt v + L / 3 ≤ t →
      (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
        4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by sorry

end TroppMatrixConcentration
