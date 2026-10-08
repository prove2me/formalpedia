-- Prove2me | Theorems.Thm_TroppMatrixConcentration_bernstein_mgf_cgf
-- name    : TroppMatrixConcentration.bernstein_mgf_cgf
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:51:38.988154+00:00
-- url     : https://prove2.me/theorems/1b02a905-fe3f-4f08-a6e4-56825b46fa2c
-- title:
--   Lemma 6.6.2 — Matrix Bernstein mgf and cgf bounds
-- statement:
--   Let $X$ be a measurable Hermitian random $d\times d$ matrix on a probability space, with $d\ge1$, finite second moment, $\mathbb EX=0$, and $\lambda_{\max}(X)\le L$ almost surely, where $L>0$. For $0<\theta<3/L$, put $g(\theta)=(\theta^2/2)/(1-\theta L/3)$. Then, in the semidefinite order,
--   $$\mathbb E e^{\theta X}\preceq\exp(g(\theta)\mathbb EX^2),\qquad\log\mathbb E e^{\theta X}\preceq g(\theta)\mathbb EX^2.$$
--   Only a one-sided eigenvalue bound is assumed. Finite second moment makes the expectation of $X^2$ well-defined under the regularity convention of Section 2.2.1.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 6.6.2, printed pp. 97–98.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem bernstein_mgf_cgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (L θ : ℝ)
    (hL : 0 < L) (hθ : 0 < θ) (hθL : θ < 3 / L)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hL2 : MemLp X 2 μ) (hMean : (∫ ω, X ω ∂μ) = 0)
    (hBound : ∀ᵐ ω ∂μ, lambdaMax (X ω) ≤ L) :
    loewnerLE (∫ ω, matrixExp (θ • X ω) ∂μ)
      (matrixExp (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ))) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ))
      (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ)) := by sorry

end TroppMatrixConcentration
