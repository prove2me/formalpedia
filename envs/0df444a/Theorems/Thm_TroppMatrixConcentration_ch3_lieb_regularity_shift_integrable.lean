-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_lieb_regularity_shift_integrable
-- name    : TroppMatrixConcentration.ch3_lieb_regularity_shift_integrable
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:20:29.62198+00:00
-- url     : https://prove2.me/theorems/f7e2b0e7-e3c6-4606-84d8-019fdda1d015
-- title:
--   Exponential integrability survives a fixed Hermitian shift
-- statement:
--   Let $H$ be a fixed Hermitian complex $d\times d$ matrix and $X$ a measurable, almost surely Hermitian random matrix of the same size on a probability space. If $e^X$ is Bochner integrable, then
--
--   $$e^{H+X}\in L^1,\qquad\operatorname{Re}\operatorname{tr}e^{H+X}\in L^1.$$
--
--   Dimension zero is allowed; integrability of $X$ itself is not required. This supplies the analytic regularity for probabilistic Lieb and its iteration over independent sums.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary regularity lemma for Corollary 3.4.2 and the proof of Lemma 3.5.1, printed pp. 35–36; standing regularity convention in Section 2.2.1, printed p. 25.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

namespace TroppMatrixConcentration

theorem ch3_lieb_regularity_shift_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    Integrable (fun ω => matrixExp (H + X ω)) μ ∧
      Integrable (fun ω => traceExp (H + X ω)) μ := by sorry

end TroppMatrixConcentration
