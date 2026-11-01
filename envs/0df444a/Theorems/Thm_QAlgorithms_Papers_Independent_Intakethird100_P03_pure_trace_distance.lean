-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_pure_trace_distance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.pure_trace_distance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:54:12.000371+00:00
-- url     : https://prove2.me/theorems/e6a2d9a5-8741-4e32-8619-8dbbc36df479
-- title:
--   §2.4.2 equation (12): pure-state trace distance
-- statement:
--   For unit vectors $\xi,\eta$ in any finite complex Hilbert space,
--
--   $$
--   \bigl\||\xi\rangle\langle\xi|-|\eta\rangle\langle\eta|\bigr\|_{\mathrm{tr}}
--   =2\sqrt{1-|\langle\xi|\eta\rangle|^2}
--   \le2\|\xi-\eta\|_2.
--   $$
--
--   The left norm is the full trace norm, without a factor of one half. This relates vector implementation errors to density-operator errors.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 12, §2.4.2 equation (12): pure-state trace distance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.12, equation (12): full trace norm, without a factor of one half. -/
theorem pure_trace_distance {I : Type*} [Fintype I] [DecidableEq I]
    (x y : EuclideanSpace ℂ I) (hx : IsState x) (hy : IsState y) :
    traceNorm (pureDensity x - pureDensity y) =
      2 * Real.sqrt (1 - ‖inner ℂ x y‖ ^ 2) ∧
    traceNorm (pureDensity x - pureDensity y) ≤ 2 * ‖x - y‖ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
