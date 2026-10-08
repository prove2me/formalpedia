-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_tail_spectral_comparison
-- name    : TroppMatrixConcentration.ch3_tail_spectral_comparison
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:08:36.758989+00:00
-- url     : https://prove2.me/theorems/6622c77a-90a0-444b-83da-22ed34339877
-- title:
--   Trace exponential dominates exponentials of extremal eigenvalues
-- statement:
--   Let $A$ be a Hermitian complex $d\times d$ matrix with $d\ge1$ and $\theta\in\mathbb R$. Then $\operatorname{tr}e^{\theta A}\ge0$, and
--
--   $$e^{\theta\lambda_{\max}(A)}\le\operatorname{tr}e^{\theta A}\quad(\theta>0),\qquad e^{\theta\lambda_{\min}(A)}\le\operatorname{tr}e^{\theta A}\quad(\theta<0).$$
--
--   The trace is its real part. This deterministic comparison is the spectral step in both matrix Laplace bounds.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Section 3.2, equation (3.2.3) and the lower-tail proof, printed p. 33.

import Definitions.Def_TroppMatrixConcentration_spectral

open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

theorem ch3_tail_spectral_comparison {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    0 ≤ traceExp (θ • A) ∧
    (0 < θ → Real.exp (θ * lambdaMax A) ≤ traceExp (θ • A)) ∧
    (θ < 0 → Real.exp (θ * lambdaMin A) ≤ traceExp (θ • A)) := by sorry

end TroppMatrixConcentration
