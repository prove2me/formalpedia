-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch4_rademacher_mgf_cgf
-- name    : TroppMatrixConcentration.ch4_rademacher_mgf_cgf
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:46:03.641575+00:00
-- url     : https://prove2.me/theorems/12ecf74d-4316-4986-95c4-c48f6f2d1415
-- title:
--   Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds
-- statement:
--   Let $A$ be a fixed Hermitian complex $d\times d$ matrix, $d\ge1$, and let $g$ be a measurable Rademacher random variable on a probability space, taking $-1$ and $1$ with probabilities one half each. For every real $\theta$,
--   $$\mathbb E e^{\theta gA}\preceq e^{\theta^2 A^2/2},\qquad\log\mathbb E e^{\theta gA}\preceq\theta^2 A^2/2.$$
--   Both relations are in positive-semidefinite order. The actual two-point distribution is required, not merely its mean and variance. No sign restriction is placed on $\theta$.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 4.6.3, printed p. 54.

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch4_rademacher_mgf_cgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hMeas : Measurable g) (hLaw : rademacherLaw μ g) (θ : ℝ) :
    loewnerLE (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) (matrixExp ((θ ^ 2 / 2) • A ^ 2)) ∧
    loewnerLE (matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ)) ((θ ^ 2 / 2) • A ^ 2) := by sorry

end TroppMatrixConcentration
