-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_lemma14
-- name    : QAlgorithms.Papers.Independent.Support50.P15.lemma14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:52:18.164339+00:00
-- url     : https://prove2.me/theorems/03a006d7-fb8b-4f35-99da-65437a6e5379
-- title:
--   lemma14
-- statement:
--   For finite $d\ge2$ and $\Delta\in[-\log d,\log d]$, let $M$ be Eq. (6) and $N(d)>0$ be the maximum of $r(1-r)[\log(((1-r)/r)(d-1))]^2$ for $0<r<1/2$. Then
--
--   $$M(\Delta,d)\ge N(d)\left(e^{\Delta/N(d)}-1-\frac{\Delta}{N(d)}\right).$$
--
--   The prefactor multiplies the whole parenthesis, and the infinite right endpoint of $M$ remains in the domain. This provides the optimal-parameter exponential lower bound used in Theorem 2.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 23, lemma14

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Lemma 14, Eq. (81), PDF p.23. N(d) multiplies the whole parenthesis. -/
theorem lemma14 {d : ℕ} (hd : 2 ≤ d) (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (-Real.log d) (Real.log d)) :
    (exponentialBound (maxVariance d) delta : EReal) ≤ tightBound d delta := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
