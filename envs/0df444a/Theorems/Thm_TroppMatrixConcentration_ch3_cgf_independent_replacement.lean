-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_cgf_independent_replacement
-- name    : TroppMatrixConcentration.ch3_cgf_independent_replacement
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:20:25.782987+00:00
-- url     : https://prove2.me/theorems/38ab8bd9-9268-48ae-ba88-97083c0107e0
-- title:
--   Lieb replacement for an independent random matrix offset
-- statement:
--   Let $H$ and $X$ be independent measurable, almost surely Hermitian random complex $d\times d$ matrices on a probability space, with $d\ge1$. Assume $e^X$ is Bochner integrable, and both trace-exponential expressions below are integrable. Put $L=\log\mathbb Ee^X$. Then
--
--   $$\mathbb E\operatorname{tr}e^{H+X}\le\mathbb E\operatorname{tr}e^{H+L}.$$
--
--   Traces mean their real parts. The offset $H$ is random; independence permits probabilistic Lieb to be applied at each value of the offset. This is the one-summand replacement step used to derive cgf subadditivity.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Proof of Lemma 3.5.1, printed pp. 35–36, applying Corollary 3.4.2.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

theorem ch3_cgf_independent_replacement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeasH : Measurable H) (hMeasX : Measurable X)
    (hHermH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hHermX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hIndep : IndepFun H X μ)
    (hExpX : Integrable (fun ω => matrixExp (X ω)) μ)
    (hIntTotal : Integrable (fun ω => traceExp (H ω + X ω)) μ)
    (hIntReplaced : Integrable (fun ω =>
      traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ))) μ) :
    (∫ ω, traceExp (H ω + X ω) ∂μ) ≤
      ∫ ω, traceExp (H ω + matrixLog (∫ u, matrixExp (X u) ∂μ)) ∂μ := by sorry

end TroppMatrixConcentration
