-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_visible_encoder_extreme_points
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.visible_encoder_extreme_points
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:37:06.701649+00:00
-- url     : https://prove2.me/theorems/e1d93cef-064b-4a1d-ba8d-87e32c1a46ea
-- title:
--   Lemma 5, (28): extreme visible encoders
-- statement:
--   Let $\mathcal K$ be a nonzero finite-dimensional complex Hilbert space and $\Xi$ any label set, possibly empty or infinite. Let $\mathcal E$ be the set of all maps $F:\Xi\to\mathcal S(\mathcal K)$, where $\mathcal S(\mathcal K)$ consists of positive semidefinite trace-one operators. With real convexity,
--
--   $$\operatorname{Ext}(\mathcal E)=\{F\in\mathcal E:\ F(i)\text{ is pure for every }i\},\qquad \operatorname{conv}(\operatorname{Ext}(\mathcal E))=\mathcal E.$$
--
--   Pure means $F(i)=|v_i\rangle\langle v_i|$ for a unit vector $v_i$. The convex hull uses finite convex combinations. This describes arbitrary visible state maps without requiring a channel extension.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 5, Lemma 5, (28): extreme visible encoders

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 5, PDF p.5, (28): extreme visible encoders are exactly pointwise
pure maps, and their real convex hull is the entire visible-encoder set. -/
theorem visible_encoder_extreme_points (L : Type*) (m : ℕ) (hm : 0 < m) :
    extremeEncoders L m = {F | F ∈ visibleEncoders L m ∧ ∀ i, IsPure (F i)} ∧
    convexHull ℝ (extremeEncoders L m) = visibleEncoders L m := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
