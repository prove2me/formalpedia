-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma2_rademacherKhintchine
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma2_rademacherKhintchine
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:03:49.275983+00:00
-- url     : https://prove2.me/theorems/bcedce3b-e0af-4ae8-ba7f-2112ed8ac0c9
-- title:
--   Lemma 2 (Standard Khintchine inequality)
-- statement:
--   Let $a=(a_i)_{i<n}$ be any real vector and let $\sigma_i$ be independent signs uniform in $\{-1,1\}$. Then
--   $$\frac{\sqrt{\sum_{i<n}a_i^2}}{\sqrt2}\le\mathbb E_\sigma\left|\sum_{i<n}a_i\sigma_i\right|\le\sqrt{\sum_{i<n}a_i^2}.$$
--   Both bounds use the same sign law. The empty vector gives zero throughout.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 24, Lemma 2 (Standard Khintchine inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Paper p.24, A41: the two-sided scalar Rademacher Khintchine inequality.
The finite sign average is exactly the iid uniform sign law. -/
theorem lemma2_rademacherKhintchine (n : ℕ) (a : Fin n → ℝ) :
    let rms := Real.sqrt (∑ i, a i ^ 2)
    let avg := signAverage n (fun sigma => |∑ i, a i * rademacherValue (sigma i)|)
    rms / Real.sqrt 2 ≤ avg ∧ avg ≤ rms := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
