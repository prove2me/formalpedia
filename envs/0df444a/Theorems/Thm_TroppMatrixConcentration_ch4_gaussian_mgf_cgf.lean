-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch4_gaussian_mgf_cgf
-- name    : TroppMatrixConcentration.ch4_gaussian_mgf_cgf
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:45:36.306983+00:00
-- url     : https://prove2.me/theorems/c95024e1-53b2-4e90-9454-e60ee128bf7f
-- title:
--   Lemma 4.6.2 — Gaussian matrix mgf and cgf identities
-- statement:
--   Let $A$ be a fixed Hermitian complex $d\times d$ matrix, $d\ge1$, and let $g$ be a measurable standard real normal random variable on a probability space. For every real $\theta$,
--   $$\mathbb E e^{\theta gA}=e^{\theta^2 A^2/2},\qquad\log\mathbb E e^{\theta gA}=\theta^2 A^2/2.$$
--   The scalar distribution is specified by its actual pushforward Gaussian probability measure with mean zero and variance one. Expectations are Bochner integrals; matrix exponential integrability follows from this law and is part of the proof obligation. No restriction on the sign of $\theta$ or on the Hermitian eigenvalues is imposed.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 4.6.2, printed pp. 52–53.

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch4_gaussian_mgf_cgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hMeas : Measurable g) (hLaw : standardGaussianLaw μ g) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) ∧
    matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = ((θ ^ 2 / 2) • A ^ 2) := by sorry

end TroppMatrixConcentration
