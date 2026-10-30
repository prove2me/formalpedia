-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_gue_two_largest_law
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.gue_two_largest_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:31:57.832636+00:00
-- url     : https://prove2.me/theorems/7ae040e4-7b79-45ca-b685-441021d8f8b5
-- title:
--   Lemma C.1: d=2 traceless GUE largest-eigenvalue law
-- statement:
--   Let $G$ be the trace-centered $2$-by-$2$ GUE matrix, with diagonal variance 1 and off-diagonal real and imaginary coordinate variance $1/2$. If $Z_1,Z_2,Z_3$ are independent standard real normal variables, then
--   $$\sqrt2\,\lambda_{\max}(G)\ \overset{\mathrm{law}}=\sqrt{Z_1^2+Z_2^2+Z_3^2},\qquad\mathbb E\lambda_{\max}(G)=\frac2{\sqrt\pi}.$$
--   The largest eigenvalue is integrable. This pins both its full chi-distribution scaling and its mean, with the source's stray $X$ renamed to $G$.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 60, Lemma C.1: d=2 traceless GUE largest-eigenvalue law

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Lemma C.1, PDF p.60: sqrt(2)*lambda_max has the chi_3 law, and its expectation
is 2/sqrt(pi). The printed X/G mismatch is corrected to the same random matrix. -/
theorem gue_two_largest_law :
    Measure.map (fun x => Real.sqrt 2 * gueSpectrum 2 x 0)
      (normalCoordinates (Fin 2 × Fin 2)) =
      Measure.map (fun x : Fin 3 → ℝ => Real.sqrt (∑ i, x i ^ 2))
        (normalCoordinates (Fin 3)) ∧
    Integrable (fun x => gueSpectrum 2 x 0) (normalCoordinates (Fin 2 × Fin 2)) ∧
    expectedLargest 2 (by omega) = 2/Real.sqrt Real.pi := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
