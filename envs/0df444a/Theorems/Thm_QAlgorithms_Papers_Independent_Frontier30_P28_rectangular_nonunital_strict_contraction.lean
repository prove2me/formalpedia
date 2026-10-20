-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_rectangular_nonunital_strict_contraction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.rectangular_nonunital_strict_contraction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:17:54.825379+00:00
-- url     : https://prove2.me/theorems/6d87de7e-47d3-4909-91dc-7851ec32ab69
-- title:
--   Strictly contractive nonunital rectangular CPTP maps
-- statement:
--   For every integer $n\ge2$ and every exponent $1<p\le\infty$, there is a complex-linear completely positive trace-preserving map $T:M_n\to M_{n^2}$, with ordinary trace, such that
--
--   $$
--   T(I_n)\ne I_{n^2},\qquad \|T\|_{p-p}<1.
--   $$
--
--   The induced norm is taken on all complex matrices with the Schatten $p$ norm, and the infinity endpoint uses the spectral operator norm. Thus the square-dimension unitality characterization does not extend to rectangular maps. The trace endpoint is excluded, because every positive trace-preserving map has induced trace norm one.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 3, §II, paragraph spanning PDF pp.3–4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Unnumbered rectangular-map existence result, source PDF pp.3–4.
The discussion concerns p > 1; strict trace-norm contraction is excluded by
the p.3 endpoint equality. No claim is made for arbitrary unequal n,r. -/
theorem rectangular_nonunital_strict_contraction
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p) :
    ∃ T : Lin n (n ^ 2),
      QAlgorithms.Entanglement.IsCompletelyPositive T ∧
      TracePreserving T ∧ T (1 : M n) ≠ (1 : M (n ^ 2)) ∧
      inducedPNorm p T < 1 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
