-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch5_chernoff_mgf_cgf
-- name    : TroppMatrixConcentration.ch5_chernoff_mgf_cgf
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:48:23.42538+00:00
-- url     : https://prove2.me/theorems/8774be6e-1c07-4c23-b8e1-d6c4b6946afb
-- title:
--   Lemma 5.4.1 — Matrix Chernoff mgf and cgf bounds
-- statement:
--   Let $X$ be a measurable random complex $d\times d$ matrix on a probability space, $d\ge1$, Hermitian almost surely. Assume $0\le\lambda_{\min}(X)$ and $\lambda_{\max}(X)\le L$ almost surely, for a common $L\ge0$. For every real $\theta$, put $c=(e^{\theta L}-1)/L$ when $L>0$, and $c=\theta$ when $L=0$. Then
--   $$\mathbb E e^{\theta X}\preceq\exp(c\mathbb EX),\qquad\log\mathbb E e^{\theta X}\preceq c\mathbb EX.$$
--   All expectations are Bochner integrals; boundedness supplies integrability. Both signs of $\theta$, as well as $\theta=0$, are included. At $L=0$ the matrix $X$ vanishes almost surely and the displayed relations have their deterministic interpretation.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 5.4.1, printed p. 70.

import Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch5_chernoff_mgf_cgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hBound : ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X ω) ∧ lambdaMax (X ω) ≤ L)
    (θ : ℝ) :
    loewnerLE (∫ ω, matrixExp (θ • X ω) ∂μ)
      (matrixExp (chernoffCgfCoefficient L θ • (∫ ω, X ω ∂μ))) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ))
      (chernoffCgfCoefficient L θ • (∫ ω, X ω ∂μ)) := by sorry

end TroppMatrixConcentration
