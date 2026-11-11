-- Prove2me | Theorems.Thm_TsybakovLearning_OptimalERM_theorem_1
-- name    : TsybakovLearning.OptimalERM.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:28.700938+00:00
-- url     : https://prove2.me/theorems/4373bc65-4abb-43e8-8a0c-10c1fd9ab03f
-- title:
--   Theorem 1 — optimal excess risk for every empirical risk minimizer
-- statement:
--   There is a universal numerical $C>1$, independent of all instance data and noise parameters, with the following property. Let $X$ be any measurable instance space and $H\subseteq\{0,1\}^X$ any class of finite VC dimension $d$ under the paper's measurable empirical-process convention. Let $D$ be a probability law satisfying Definition 1 with $a\ge1$, $0<\alpha<1$ and Bayes rule $h_D^*\in H$. For every $n\ge1$ and $0<\delta<1$, with probability at least $1-\delta$ over the i.i.d. sequence $S\sim D^n$,
--
--   $$\forall h\in\mathrm{ERM}(H;S),\qquad \mathrm{er}_D(h)-\mathrm{er}_D(h_D^*)\le C\left(\frac{a(d+L(1/\delta))}{(1-\alpha)n}\right)^{1/(2-\alpha)},\qquad L(x)=\log_2(\max\{x,2\}).$$
--
--   Every empirical minimizer in the original H is covered on one event, with unrestricted ties. There is no sample-size logarithm. This is the source's sharp upper-bound theorem; Theorem 2 restates it and supplies the witness formula $C=4096c_0^2+192c_0+1$ from the universal Lemma 2 constant.
--
--   **Formalization Note** The theorem assumes neither concentration milestone nor its conclusion. Risks are genuine bounded measurable 0–1 expectations. The class may be uncountable; neither X nor H is restricted to finite, discrete, Euclidean, or pointwise-separable models. Measurability of every ERM tail event is explicit, independently of C. No single ERM selection is introduced, and d=0 is retained.
--
--   Differences from the source:
--   - encoding: a numerical C greater than 1 → an existential C greater than 1 before every instance type and data; reason: matches universality; Theorem 2 gives C=4096 c0 squared +192 c0 +1, but Theorem 1 itself requests only existence
--   - reading: measurable class and ordinary probability convention → measurable hypotheses, measurable finite signed empirical suprema for the restricted localized and centered loss-difference classes, and measurable exact failure or tail events for all thresholds; reason: makes Lemma 2 and Appendix A measurability explicit without countability, pointwise separability, topology, a measurable ERM selection, or any probability estimate
--   - encoding: an i.i.d. sample written with braces → Fin m (or Fin n) sequence under the genuine product law, with positive sample size; reason: retains repetitions and the original empirical denominator; division by sample size presupposes positivity
--   - encoding: with probability at least 1 minus delta, simultaneously → ordinary product probability of the measurable failure set is at most delta; reason: equivalent complementary-event formulation, with all indicated pairs or hypotheses inside one event
--   - encoding: binary class of finite VC dimension d → Bool-valued functions, a set-valued H, and UnderstandingML.vcDim H = (d : Nat-infinity), including d=0; reason: same labelings and shattering; no finite-class restriction
--   - encoding: eta is the conditional probability of label 1 and h-star is its displayed Bayes rule → a measurable [0,1]-valued regression version satisfying the joint integral identity, with Bayes prediction true at eta=1/2; reason: binary Radon–Nikodym representation works on arbitrary measurable X and ties eta to D
--   - encoding: supremum of excess risks over every empirical risk minimizer → failure means there exists an actual IsERM hypothesis whose excess exceeds the bound; reason: equivalent for nonempty H, whose integer empirical counts attain a minimum; avoids a junk real supremum and imposes no tie-breaker
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Theorem 1, p. 5 (PDF p. 5); constant provenance: Theorem 2, p. 9 (PDF p. 9)

import Definitions.Def_TsybakovLearning_OptimalERM_ProbabilityConvention

open MeasureTheory
universe uGoal

namespace TsybakovLearning.OptimalERM

/-- Theorem 1, p. 5: simultaneous over every actual empirical argmin in the original H.
Theorem 2, pp. 9–10, supplies C=4096 c₀²+192 c₀+1; no concentration is assumed here. -/
theorem theorem_1 : ∃ C : ℝ, 1 < C ∧
    ∀ (X : Type uGoal) [MeasurableSpace X] (H : Set (X → Bool))
      (D : Measure (X × Bool)) [IsProbabilityMeasure D] (R : Regression D),
      MeasurableClass H D → ∀ d : ℕ, UnderstandingML.vcDim H = (d : ℕ∞) →
      ∀ a α : ℝ, 1 ≤ a → 0 < α → α < 1 → Tsybakov H D R a α →
      ∀ n : ℕ, 0 < n → ∀ δ : ℝ, 0 < δ → δ < 1 →
      (∀ t : ℝ, MeasurableSet (ermTail H D R n t)) →
        UnderstandingML.iidLaw D n (ermFailure C H D R a α δ d n) ≤
          ENNReal.ofReal δ := by sorry

end TsybakovLearning.OptimalERM
