-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_tv_representations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.tv_representations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:34:56.719018+00:00
-- url     : https://prove2.me/theorems/27468bc3-5ef4-4702-915e-78022426869c
-- title:
--   Theorem 15: All identities (243)–(251) for TV in terms of relative information, its positive/negative parts, events under P and Q, and spectrum integrals; additionally (252),(253) under mutual absolut
-- statement:
--   Let $Z=dP/dQ$, $I=\log_b Z$, and let $F$ be the distribution function of $I$ under $P$, where $P\ll Q$ are probability measures. Write $x^+=\max(x,0)$ and $x^-=\max(-x,0)$. The full total variation $V=|P-Q|$ has all nine representations
--
--   $$\begin{aligned}V&=E_Q|1-Z|=2E_Q(1-Z)^+=2E_Q(1-Z)^-=2E_P(1-Z^{-1})^+\\
--   &=2(P[I>0]-Q[I>0])=2(Q[I\le0]-P[I\le0])\\
--   &=2\int_0^1Q[I<\log_b t]dt=2\int_0^1P[I>\log_b(1/t)]dt\\
--   &=2\int_1^{\beta_1^{-1}}t^{-2}(1-F(\log_b t))dt.\end{aligned}$$
--
--   If also $Q\ll P$, then $V=2E_P(1-Z^{-1})^-=E_P|1-Z^{-1}|$. Inverse densities may be defined arbitrarily on the $P$-null zero-density set. The upper integration endpoint is infinity when $\beta_1=0$. These are all eleven identities (243)–(253).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 35, Theorem 15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 15: All identities (243)–(251) for TV in terms of relative information, its positive/negative parts, events under P and Q, and informationSpectrum integrals; additionally (252),(253) under mutual absolute continuity. Sason--Verdu, arXiv:1508.00335v7, PDF p.35.  -/
theorem tv_representations
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    fullVariation P Q = (∫⁻ x, ENNReal.ofReal |1 - rnDensityReal P Q x| ∂Q) ∧
    fullVariation P Q = 2 * (∫⁻ x, ENNReal.ofReal (max (1 - rnDensityReal P Q x) 0) ∂Q) ∧
    fullVariation P Q = 2 * (∫⁻ x, ENNReal.ofReal (max (rnDensityReal P Q x - 1) 0) ∂Q) ∧
    fullVariation P Q = 2 * (∫⁻ x, ENNReal.ofReal (max (1 - (rnDensityReal P Q x)⁻¹) 0) ∂P) ∧
    fullVariation P Q = 2 * (P {x | 0 < relativeInfo b P Q x} - Q {x | 0 < relativeInfo b P Q x}) ∧
    fullVariation P Q = 2 * (Q {x | relativeInfo b P Q x ≤ 0} - P {x | relativeInfo b P Q x ≤ 0}) ∧
    fullVariation P Q = 2 * (∫⁻ t in Ioo (0 : ℝ) 1, Q {x | relativeInfo b P Q x < elogB b (ENNReal.ofReal t)}) ∧
    fullVariation P Q = 2 * (∫⁻ t in Ioo (0 : ℝ) 1, P {x | elogB b ((ENNReal.ofReal t)⁻¹) < relativeInfo b P Q x}) ∧
    fullVariation P Q = 2 * (∫⁻ t in {t : ℝ | 1 < t ∧ ENNReal.ofReal t < upperDensity P Q},
      ENNReal.ofReal (t ^ (-2 : ℤ)) * (1 - informationSpectrum b P Q (elogB b (ENNReal.ofReal t)))) ∧
    (Q ≪ P → fullVariation P Q = 2 * (∫⁻ x, ENNReal.ofReal (max ((rnDensityReal P Q x)⁻¹ - 1) 0) ∂P) ∧
      fullVariation P Q = (∫⁻ x, ENNReal.ofReal |1 - (rnDensityReal P Q x)⁻¹| ∂P)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
