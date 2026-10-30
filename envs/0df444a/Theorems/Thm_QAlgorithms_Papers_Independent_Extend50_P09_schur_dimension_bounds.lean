-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_schur_dimension_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.schur_dimension_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:26:25.993738+00:00
-- url     : https://prove2.me/theorems/e340cf9f-7176-4eba-abdc-4bd6b5f69fcf
-- title:
--   §IV A1: polynomial Schur dimension and multinomial Specht bounds
-- statement:
--   Let $d,n$ be positive integers and $\lambda$ a partition of $n$ with at most $d$ rows, padded by zero rows. Let $l_\lambda=\dim L_\lambda$ and $r_\lambda=\dim R_\lambda$ be the actual Schur and Specht module dimensions. Then
--   $$l_\lambda\le\prod_{i=1}^d\binom{\lambda_i+d-1}{d-1}\le(n+d)^{d(d-1)},$$
--   $$\frac{n!}{\prod_{i=1}^d((\lambda_i+d)!/d!)}\le r_\lambda\le\frac{n!}{\prod_{i=1}^d\lambda_i!}.$$
--
--   For fixed $d$ these exhibit polynomial Schur dimension and the multinomial Specht bounds, using constructed modules rather than arbitrary dimension certificates.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 9, §IV A1: polynomial Schur dimension and multinomial Specht bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- §IV A1, PDF pp.9–10, (67),(69),(70): actual Schur and Specht
module dimensions; zero-padded rows and fixed positive alphabet dimension.
SOURCE CORRECTION: printed (70) has n in its numerator; use n! as required
by the hook-length formula (66), bound (68), and the same line's multinomial
expression. No other part of the inequality is changed. -/
theorem schur_dimension_bounds (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (lam : Schur.Partition d n) :
    (ldim lam : ℝ) ≤ ∏ i : Fin d,
      ((lam.val.rowLen i.val + d - 1).choose (d-1) : ℝ) ∧
    (∏ i : Fin d, ((lam.val.rowLen i.val + d - 1).choose (d-1) : ℝ)) ≤
      ((n+d : ℕ) : ℝ)^(d*(d-1)) ∧
    (rdim lam : ℝ) ≤ (n.factorial : ℝ) /
      (∏ i : Fin d, ((lam.val.rowLen i.val).factorial : ℝ)) ∧
    (n.factorial : ℝ) /
      (∏ i : Fin d, (((lam.val.rowLen i.val + d).factorial : ℝ) / (d.factorial : ℝ))) ≤
      (rdim lam : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
