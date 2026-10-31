-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_single_crossing_expectation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.single_crossing_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:43:11.067687+00:00
-- url     : https://prove2.me/theorems/c1aae97f-919d-44e3-b8f6-5fd77bc300af
-- title:
--   Lemma 5: For nonnegative increasing g on [a,b] and probability densities p1,p2 there with p1>=p2 on [a,c], p1<p2 on (c,b], E[g(W)]<=E[g(V)]
-- statement:
--   Let $a<c<b$ and let $g$ be nonnegative and increasing on $[a,b]$. Let $p_1,p_2$ be measurable probability densities supported on this interval. Suppose $p_1\ge p_2$ on $[a,c]$ and $p_1<p_2$ on $(c,b]$. Then
--
--   $$E_{p_1}g\le E_{p_2}g.$$
--
--   The weak first and strict second crossing conditions are retained. Since $g$ is bounded by its endpoint values, both expectations are finite; interval-restricted densities represent the supported laws without extra conditions outside the interval.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 87, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Lemma 5: For nonnegative increasing g on [a,b] and probability densities p1,p2 there with p1>=p2 on [a,c], p1<p2 on (c,b], E[g(W)]<=E[g(V)]. Sason--Verdu, arXiv:1508.00335v7, PDF p.87.  -/
theorem single_crossing_expectation
    (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (g p1 p2 : ℝ → ℝ) (hg : MonotoneOn g (Icc a b))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t) (hp1 : Measurable p1) (hp2 : Measurable p2)
    (hp10 : ∀ t ∈ Icc a b, 0 ≤ p1 t) (hp20 : ∀ t ∈ Icc a b, 0 ≤ p2 t)
    (hn1 : ∫⁻ t in Icc a b, ENNReal.ofReal (p1 t) = 1)
    (hn2 : ∫⁻ t in Icc a b, ENNReal.ofReal (p2 t) = 1)
    (hleft : ∀ t ∈ Icc a c, p2 t ≤ p1 t)
    (hright : ∀ t ∈ Ioc c b, p1 t < p2 t) :
    (∫⁻ t in Icc a b, ENNReal.ofReal (g t) * ENNReal.ofReal (p1 t)) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (g t) * ENNReal.ofReal (p2 t) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
