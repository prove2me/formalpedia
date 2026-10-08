-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_probabilistic_lieb
-- name    : TroppMatrixConcentration.ch3_probabilistic_lieb
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:44:33.646987+00:00
-- url     : https://prove2.me/theorems/712d622b-a02f-4a3f-b441-c8223b149c8a
-- title:
--   Corollary 3.4.2 — Probabilistic Lieb inequality
-- statement:
--   Let $H$ be a fixed Hermitian matrix and $X$ a measurable, almost-surely Hermitian random matrix of the same positive dimension on a probability space. If $e^X$ is Bochner integrable, then
--   $$\mathbb E\operatorname{tr}\exp(H+X)\le\operatorname{tr}\exp\!\left(H+\log\mathbb E e^X\right).$$
--   This is the probabilistic form of Lieb's concavity theorem used in the trace-cgf subadditivity argument. No independence hypothesis or integrability of $X$ itself is required.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Corollary 3.4.2, printed p. 35.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch3_probabilistic_lieb {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    (∫ ω, traceExp (H + X ω) ∂μ) ≤
      traceExp (H + matrixLog (∫ ω, matrixExp (X ω) ∂μ)) := by sorry

end TroppMatrixConcentration
