-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_entropy_spectrum_integrals
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.entropy_spectrum_integrals
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:35:20.858599+00:00
-- url     : https://prove2.me/theorems/c3e809af-e0e3-4f1b-aad7-610ac37057f9
-- title:
--   Theorem 16: D equals integral_0^infinity(1-F(a))da-integral_-infinity^0 F(a)da, and the transformed identities (256),(257)
-- statement:
--   Let $D(P\|Q)<\infty$ and let $F$ be the relative information CDF under $P$. Then
--
--   $$D(P\|Q)=\int_0^\infty[1-F(a)]da-\int_{-\infty}^0F(a)da.$$
--
--   In nats this also equals $\int_1^\infty[1-F(\ln t)]dt/t-\int_0^1F(\ln t)dt/t$, and
--
--   $$\int_0^\infty Q[I>a]a e^a da-\int_{-\infty}^0 Q[I<a]a e^a da.$$
--
--   Only the last two formulas impose natural logarithms. Nonnegative extended integrals retain the signs and avoid default-zero Bochner integrals; finiteness of KL makes the displayed differences well-defined.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 36, Theorem 16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 16: D equals integral_0^infinity(1-F(a))da-integral_-infinity^0 F(a)da, and the transformed identities (256),(257). Sason--Verdu, arXiv:1508.00335v7, PDF p.36.  -/
theorem entropy_spectrum_integrals
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hfin : kl b P Q < ∞) :
    (kl b P Q : EReal) =
      ((∫⁻ a in Ioi (0 : ℝ), 1 - informationSpectrum b P Q (a : EReal)) : EReal) -
      ((∫⁻ a in Iio (0 : ℝ), informationSpectrum b P Q (a : EReal)) : EReal) ∧
    (b.val = Real.exp 1 →
      (kl b P Q : EReal) =
        ((∫⁻ t in Ioi (1 : ℝ), (1 - informationSpectrum b P Q (elogB b (ENNReal.ofReal t))) /
          ENNReal.ofReal t) : EReal) -
        ((∫⁻ t in Ioo (0 : ℝ) 1, informationSpectrum b P Q (elogB b (ENNReal.ofReal t)) /
          ENNReal.ofReal t) : EReal) ∧
      kl b P Q =
        (∫⁻ a in Ioi (0 : ℝ), Q {x | (a : EReal) < relativeInfo b P Q x} * ENNReal.ofReal (a * Real.exp a)) +
        (∫⁻ a in Iio (0 : ℝ), Q {x | relativeInfo b P Q x < (a : EReal)} *
          ENNReal.ofReal (-a * Real.exp a))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
