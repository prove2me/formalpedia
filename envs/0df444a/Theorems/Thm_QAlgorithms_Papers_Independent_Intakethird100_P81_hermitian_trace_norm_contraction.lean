-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_hermitian_trace_norm_contraction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.hermitian_trace_norm_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:57:15.511523+00:00
-- url     : https://prove2.me/theorems/9fdafe45-d9a4-40e2-997d-0d6f2f05d213
-- title:
--   Trace-norm contraction on Hermitian inputs
-- statement:
--   Let $\rho$ be any Hermitian matrix on a finite-dimensional complex Hilbert space, and let $F$ be a complex-linear, completely positive, trace-preserving map to another finite-dimensional complex matrix space. Then
--   $$
--   \|F(\rho)\|_1\le\|\rho\|_1.
--   $$
--
--   Here the trace norm is $\operatorname{Tr}\sqrt{M^\dagger M}$, without a factor of one half. The input need not be positive or have trace one, so the statement controls signed Hermitian perturbations as well as states.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 9, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Lemma 1, PDF p.9: contraction for arbitrary Hermitian inputs, not merely states. -/
theorem hermitian_trace_norm_contraction {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho : Matrix I I ℂ) (hrho : rho.IsHermitian) (F : Superop I J)
    (hF : IsChannel F) : traceNorm (F rho) ≤ traceNorm rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
