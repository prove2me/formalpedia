-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_spectrum_lower_envelope
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.spectrum_lower_envelope
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:37:30.499024+00:00
-- url     : https://prove2.me/theorems/e806cf55-223e-4768-b766-9486682d6eeb
-- title:
--   Proposition 2: Spectrum lower bound (277): F(log beta)>=0 for 0<beta<=2/(2-TV), and >=1-beta TV/[2(beta-1)] above that threshold; the lower envelope is sharp at fixed TV
-- statement:
--   For $P\ll Q$, let $V=|P-Q|<2$. For every $t>0$,
--
--   $$F_{P\|Q}(\log_b t)\ge
--   \begin{cases}0&t\le 2/(2-V),\\1-tV/[2(t-1)]&t>2/(2-V).\end{cases}$$
--
--   For each fixed $V=2\delta$ with $0<\delta<1$, this lower envelope is an infimum over probability pairs, witnessed arbitrarily closely by binary pairs. At $\delta=0$, the only pair is $P=Q$ and the actual CDF is 0 for $t<1$ and 1 for $t\ge1$. The paper attributes the bound to Liu–Cuff–Verdu [68, Proposition 2]. The printed universal attainment clause is corrected to infimal sharpness, as its own limiting proof requires. For 0<delta<1 and 0<t<1/(1-delta), the envelope value 0 is attained exactly by a binary pair, as in the first branch of the source proof. This exact-attainment regime is retained in the formal statement.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 39, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Proposition 2: Spectrum lower bound (277): F(log inverseUpperDensity)>=0 for 0<inverseUpperDensity<=2/(2-TV), and >=1-inverseUpperDensity TV/[2(inverseUpperDensity-1)] above that threshold; the lower envelope is sharp at fixed TV. Sason--Verdu, arXiv:1508.00335v7, PDF p.39. Source correction: retain exact attainment for 0<delta<1 and beta<1/(1-delta); at and above that cutoff use infimal sharpness. Delta=0 has the separate exact CDF. The printed inequality is unchanged. The proof takes a limit at the strict-tail boundary. -/
theorem spectrum_lower_envelope
    (b : LogBase) :
    (∀ {A : Type u} [MeasurableSpace A] (P Q : Measure A)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q], P ≪ Q →
      ∀ t : ℝ, 0 < t → ENNReal.ofReal (spectrumEnvelope (fullVariation P Q).toReal t) ≤
        informationSpectrum b P Q (elogB b (ENNReal.ofReal t))) ∧
    (∀ d t : ℝ, 0 < d → d < 1 → 0 < t → t < 1 / (1 - d) →
      ∃ P Q : Measure Bool, IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ P ≪ Q ∧
        fullVariation P Q = ENNReal.ofReal (2 * d) ∧
        informationSpectrum b P Q (elogB b (ENNReal.ofReal t)) = 0) ∧
    (∀ d t e : ℝ, 0 < d → d < 1 → 0 < t → 0 < e →
      ∃ P Q : Measure Bool, IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ P ≪ Q ∧
        fullVariation P Q = ENNReal.ofReal (2 * d) ∧
        informationSpectrum b P Q (elogB b (ENNReal.ofReal t)) <
          ENNReal.ofReal (spectrumEnvelope (2 * d) t + e)) ∧
    (∀ {A : Type u} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P],
      ∀ t : ℝ, 0 < t → informationSpectrum b P P (elogB b (ENNReal.ofReal t)) = if t < 1 then 0 else 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
