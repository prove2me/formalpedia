-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_spectrum_kl_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.spectrum_kl_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:47:38.741085+00:00
-- url     : https://prove2.me/theorems/561c6351-6552-4cc4-9173-bf8b64b01ebb
-- title:
--   Theorem 34: For beta>1, (1-F(log beta))/D<=u(beta)=min_(1<gamma<beta) beta c_gamma/(beta-gamma); u is decreasing and u(beta)<=2/log(beta/(2e)) for beta>2e
-- statement:
--   For $\beta>1$, define the attained open-interval minimum
--
--   $$u(\beta)=\min_{1<\gamma<\beta}\frac{\beta c_\gamma}{\beta-\gamma}.$$
--
--   For every distinct probability pair $P\ll Q$, $1-F_{P\|Q}(\log_b\beta)\le u(\beta)D(P\|Q)$. The function $u$ is decreasing on $(1,\infty)$ and $u(\beta)\le2/\log_b(\beta/(2e))$ for $\beta>2e$, with natural $e$. The multiplicative comparison avoids dividing an infinite entropy.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 65, Theorem 34

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 34: For inverseUpperDensity>1, (1-F(log inverseUpperDensity))/D<=u(inverseUpperDensity)=min_(1<gamma<inverseUpperDensity) inverseUpperDensity c_gamma/(inverseUpperDensity-gamma); u is decreasing and u(inverseUpperDensity)<=2/log(inverseUpperDensity/(2e)) for inverseUpperDensity>2e. Sason--Verdu, arXiv:1508.00335v7, PDF p.65.  -/
theorem spectrum_kl_bound
    (b : LogBase) :
    (∀ t : ℝ, 1 < t → IsLeast
      ((fun g : ℝ => t * hockeyKLConstant b g / (t - g)) '' Ioo 1 t) (spectrumCoefficient b t)) ∧
    AntitoneOn (spectrumCoefficient b) (Ioi 1) ∧
    (∀ t : ℝ, 2 * Real.exp 1 < t →
      spectrumCoefficient b t ≤ 2 / logB b (t / (2 * Real.exp 1))) ∧
    (∀ {A : Type u} [MeasurableSpace A] (P Q : Measure A)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q], P ≪ Q → P ≠ Q →
      ∀ t : ℝ, 1 < t → 1 - informationSpectrum b P Q (elogB b (ENNReal.ofReal t)) ≤
        ENNReal.ofReal (spectrumCoefficient b t) * kl b P Q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
