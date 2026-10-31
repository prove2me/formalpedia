-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:51:02.270744+00:00
-- url     : https://prove2.me/theorems/f47a6aaa-b442-4a2c-a199-185198391ccf
-- title:
--   Basic E-gamma properties (399)–(405) and optimal ratio constant
-- statement:
--   For $P\ll Q$ and $\gamma\ge1$, with $I=\log_b(dP/dQ)$,
--
--   $$E_\gamma(P\|Q)=P[I>\log_b\gamma]-\gamma Q[I>\log_b\gamma]
--   =\max_F\{P(F)-\gamma Q(F)\}.$$
--
--   If $\gamma_1\ge\gamma_2\ge1$, then $E_{\gamma_1}\le E_{\gamma_2}$ with best universal coefficient 1. If $P\ll R\ll Q$ and $s,t\ge1$, then $E_{st}(P\|Q)\le E_s(P\|R)+sE_t(R\|Q)$, and $E_\gamma(P\|Q)\le E_\gamma(R\|Q)+|P-R|/2$. The event maximum is attained and the sharp monotonicity comparison is multiplicative at a zero denominator.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 57, Basic E-gamma properties (399)–(405) and optimal ratio constant

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Basic E-gamma properties (399)–(405) and optimal ratio constant. Sason--Verdu, arXiv:1508.00335v7, PDF p.57.  -/
theorem hockey_properties
    (g g1 g2 : ℝ) (hg : 1 ≤ g) (h1 : g2 ≤ g1) (h2 : 1 ≤ g2)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    (hockey g P Q).toReal = (P {x | (ENNReal.ofReal g) < P.rnDeriv Q x}).toReal -
      g * (Q {x | (ENNReal.ofReal g) < P.rnDeriv Q x}).toReal ∧
    IsGreatest {z : ℝ | ∃ F : Set A, MeasurableSet F ∧ z = (P F).toReal - g * (Q F).toReal}
      (hockey g P Q).toReal ∧
    hockey g1 P Q ≤ hockey g2 P Q ∧
    Sharp (hockey g1) (hockey g2) acPairs 1 ∧
    (∀ (R : Measure A) [IsProbabilityMeasure R], P ≪ R → R ≪ Q →
      ∀ s t : ℝ, 1 ≤ s → 1 ≤ t →
        hockey (s * t) P Q ≤ hockey s P R + ENNReal.ofReal s * hockey t R Q) ∧
    (∀ (R : Measure A) [IsProbabilityMeasure R], P ≪ R → R ≪ Q →
      hockey g P Q ≤ hockey g R Q + fullVariation P R / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
