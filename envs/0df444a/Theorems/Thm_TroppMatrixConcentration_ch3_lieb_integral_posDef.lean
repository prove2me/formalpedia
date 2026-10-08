-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch3_lieb_integral_posDef
-- name    : TroppMatrixConcentration.ch3_lieb_integral_posDef
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T14:20:31.564107+00:00
-- url     : https://prove2.me/theorems/7937a5c3-bf89-4d5a-ba7e-36efb6ff6f75
-- title:
--   Expectation of an almost surely positive-definite matrix
-- statement:
--   Let $Z$ be a Bochner-integrable random complex $d\times d$ matrix on a probability space. If $Z$ is positive definite almost surely, then
--
--   $$\mathbb EZ\succ0.$$
--
--   No uniform lower eigenvalue bound is assumed. Dimension zero is permitted. This auxiliary lemma keeps the mean inside the positive-definite domain when applying Jensen’s inequality to Lieb’s concave function.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary positive-definite integration fact used in Corollary 3.4.2, printed p. 35; quadratic-form definition (2.1.10), printed p. 20.

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration

theorem ch3_lieb_integral_posDef {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hInt : Integrable Z μ) (hPD : ∀ᵐ ω ∂μ, (Z ω).PosDef) :
    (∫ ω, Z ω ∂μ).PosDef := by sorry

end TroppMatrixConcentration
