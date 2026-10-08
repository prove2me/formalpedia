-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_bernstein
-- name    : TroppMatrixConcentration.ch7_intrinsic_bernstein
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:53:31.23006+00:00
-- url     : https://prove2.me/theorems/af77a148-c124-49e3-b3cf-5df6024f4602
-- title:
--   Theorem 7.3.1 — Intrinsic matrix Bernstein
-- statement:
--   Let $S_k$ be a finite independent family of measurable complex $m\times n$ random matrices on a probability space, $m,n\ge1$, with $\mathbb ES_k=0$ and $\|S_k\|\le L$ almost surely, $L\ge0$. Set $Z=\sum_kS_k$. Let $V_1\succeq\mathbb EZZ^*$ and $V_2\succeq\mathbb EZ^*Z$, with at least one nonzero, and put $r=r(\operatorname{diag}(V_1,V_2))$, $v=\max\{\|V_1\|,\|V_2\|\}$. Then
--   $$\mathbb EZZ^*=\sum_k\mathbb ES_kS_k^*,\qquad\mathbb EZ^*Z=\sum_k\mathbb ES_k^*S_k,$$
--   $$\mathbb P\{\|Z\|\ge t\}\le4r\exp\!\left(-\frac{t^2/2}{v+Lt/3}\right)\qquad(t\ge\sqrt v+L/3).$$
--   The variance bounds are matrices, not merely scalar norm bounds. The nonzero block proxy keeps intrinsic dimension in the source's meaningful domain. The finite family may be empty, and deterministic zero summands remain permitted. All required moments follow from boundedness. This is the designated goal; Theorem 7.2.1 is the other main theorem in this chapter proposal.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 7.3.1, equations (7.3.1–2), printed p. 108; independence confirmed in Section 7.7.3, printed p. 117.

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch7_intrinsic_bernstein {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ)
    (hV : V₁ ≠ 0 ∨ V₂ ≠ 0)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L)
    (hVariance₁ : loewnerLE
      (∫ ω, (∑ k, S k ω) * (∑ k, S k ω).conjTranspose ∂μ) V₁)
    (hVariance₂ : loewnerLE
      (∫ ω, (∑ k, S k ω).conjTranspose * (∑ k, S k ω) ∂μ) V₂) :
    let Z := fun ω => ∑ k, S k ω
    let r := intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)
    let v := max (spectralNorm V₁) (spectralNorm V₂)
    (∫ ω, Z ω * (Z ω).conjTranspose ∂μ) =
      ∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ ∧
    (∫ ω, (Z ω).conjTranspose * Z ω ∂μ) =
      ∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ ∧
    ∀ t : ℝ, Real.sqrt v + L / 3 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
        4 * r * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by sorry

end TroppMatrixConcentration
