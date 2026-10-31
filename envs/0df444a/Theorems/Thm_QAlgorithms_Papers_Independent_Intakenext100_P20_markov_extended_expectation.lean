-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_markov_extended_expectation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.markov_extended_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:43:05.124381+00:00
-- url     : https://prove2.me/theorems/d16f2824-154b-4e41-a6cd-dd494c439179
-- title:
--   Appendix E (E1): Markov inequality with extended expectation
-- statement:
--   Let $\mu$ be a probability measure, let $X$ be a measurable positive real random variable, and let $c>0$. With expectation interpreted in $[0,+\infty]$,
--
--   $$\mu\{X\ge c\}\le\frac{\mathbb E_\mu[X]}{c},\qquad \mathbb E_\mu[X]=\int X\,d\mu.$$
--
--   The integral is the nonnegative extended Lebesgue integral. No finite-expectation hypothesis is imposed; if the expectation is infinite, the right side is infinite. Measurability is the standing meaning of random variable.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 11, Appendix E, (E1)

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

/-- Appendix E, PDF p.11, (E1): Markov's inequality for a positive random
variable. Measurability is the standing meaning of random variable. Expectation
is the nonnegative extended Lebesgue integral; no integrability restriction is
added, and an infinite expectation stays infinite. -/
theorem markov_extended_expectation {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (X : Omega → ℝ) (hX : Measurable X) (hpos : ∀ w, 0 < X w)
    (c : ℝ) (hc : 0 < c) :
    mu {w | c ≤ X w} ≤
      MeasureTheory.lintegral mu (fun w => ENNReal.ofReal (X w)) / ENNReal.ofReal c := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
