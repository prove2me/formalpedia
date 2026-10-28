-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_lemma15
-- name    : QAlgorithms.Papers.Independent.Support50.P15.lemma15
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:53:10.239043+00:00
-- url     : https://prove2.me/theorems/c7853185-3268-423d-bc46-95b0a21f1c63
-- title:
--   lemma15
-- statement:
--   For each integer $d\ge2$, let $N(d)=\max_{0<r<1/2}r(1-r)[\log(((1-r)/r)(d-1))]^2$ and $N_d=\tfrac14\log^2(d-1)+1$. Then
--
--   $$N_d-1=\tfrac14\log^2(d-1)<N(d)<N_d,\qquad N(d)<\log^2d.$$
--
--   All inequalities are strict, including at $d=2$ where $\log(d-1)=0$ but $N(2)>0$. These provide computable upper and lower estimates for the optimal variance and relative-entropy constants.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 23, lemma15

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Lemma 15, Eqs. (85)--(86), PDF pp.23--24, with strict bounds also at d=2. -/
theorem lemma15 {d : ℕ} (hd : 2 ≤ d) :
    (Real.log ((d : ℝ) - 1)) ^ 2 / 4 < maxVariance d ∧
    maxVariance d < easyVariance d ∧ maxVariance d < (Real.log d) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
