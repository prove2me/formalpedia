-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_associated_zero_tail
-- name    : QuadraticProbe717.Insertion.associated_zero_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:42.137148+00:00
-- url     : https://prove2.me/theorems/87ae335b-9d0d-47a9-b5fc-fbbca29541ac
-- title:
--   Lemma 5.2 — zero tail for associated indicators
-- statement:
--   Let $X_1,\ldots,X_s$ be positively associated measurable indicators. Put $S=\sum_iX_i$, $\mu=\mathbb E[S]>0$ and $d=\sum_{i<j}\operatorname{Cov}(X_i,X_j)$. Then
--   $$\Pr[S=0]\le e^{-\mu/8}+\frac{8d}{\mu^2}.$$
--   Both numerical eights are retained. The mean and covariance sum are computed from the given law, rather than introduced as unrelated parameters. Boundedness of indicators guarantees all their moments exist.
--
--   Differences from the source:
--   - encoding: S, μ and d defined in the statement → indicatorSum, its actual integral, and the finite pairCovarianceSum; reason: the same derived quantities, with no assumed estimates or arbitrary certificates
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 5.2; proof pp. 9–10, p. 9 (PDF p. 9)

import Definitions.Def_QuadraticProbe717_Insertion_association

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem associated_zero_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ) (X : Fin s → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hbits : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hassoc : PositivelyAssociated P X) (hmean : 0 < ∫ ω, indicatorSum s X ω ∂P) :
    (P {ω | indicatorSum s X ω = 0}).toReal ≤
      Real.exp (-(∫ ω, indicatorSum s X ω ∂P) / 8) +
      8 * pairCovarianceSum s P X / (∫ ω, indicatorSum s X ω ∂P)^2 := by sorry

end QuadraticProbe717.Insertion
