-- Prove2me | Theorems.Thm_TsybakovLearning_OptimalERM_lemma_3
-- name    : TsybakovLearning.OptimalERM.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:24.443211+00:00
-- url     : https://prove2.me/theorems/a6690897-6982-4cc2-9a11-b77c7ec5752d
-- title:
--   Lemma 3 — small-excess-risk concentration
-- statement:
--   There is one universal $c_0>0$ satisfying the full Lemma 2 property and the following bound. Let $H\subseteq\{0,1\}^X$ have finite VC dimension $d$, let $a\ge1$, $0<\alpha<1$, and suppose $D\in\mathrm{TN}_H(a,\alpha)$ with regression $\eta_D$ and Bayes rule $h_D^*$. Under the ordinary measurable empirical-process convention, for every $m\ge1$, $0<\gamma\le1$, $0<\delta<1$, with probability at least $1-\delta$ under $S\sim D^m$, every $h\in H$ satisfying $\mathrm{er}_D(h)-\mathrm{er}_D(h_D^*)\le\gamma$ obeys
--
--   $$\left|\widehat{\mathrm{er}}_S(h)-\widehat{\mathrm{er}}_S(h_D^*)-\mathrm{er}_D(h)+\mathrm{er}_D(h_D^*)\right|$$
--   $$\le16c_0\left[\sqrt{\frac{a\gamma^\alpha(d+L(1/\delta))}{(1-\alpha)m}}+\frac{d+L(1/\delta)}{(1-\alpha)m}\bigl(1+L(a)+(1-\alpha)L(1/\gamma)\bigr)^2\right].$$
--
--   Here $L(x)=\log_2(\max\{x,2\})$. The exact multiplier $16c_0$ covers the whole sum, and only the parenthesis in the linear term is squared. Both empirical errors use the same sample. This is the second milestone toward the sharp ERM guarantee.
--
--   **Formalization Note** The endpoint $\gamma=1$ and dimension $d=0$ are retained. Regression is tied to D by its integral identity, and TN is the exact all-positive-threshold predicate of Definition 1. The existence conclusion carries the same universal Bernstein property as Lemma 2, including its zero-ratio reading. No numerical value for c0 is stipulated.
--
--   Differences from the source:
--   - encoding: c0 is the same universal constant as Lemma 2 → one existential positive c0 jointly satisfies the full universal Bernstein property and the full Lemma 3 bound; reason: explicit sharing prevents per-instance witnesses; the Bernstein property is a conclusion here and is never an assumption of the goal
--   - reading: measurable class and ordinary probability convention → measurable hypotheses, measurable finite signed empirical suprema for the restricted localized and centered loss-difference classes, and measurable exact failure or tail events for all thresholds; reason: makes Lemma 2 and Appendix A measurability explicit without countability, pointwise separability, topology, a measurable ERM selection, or any probability estimate
--   - encoding: an i.i.d. sample written with braces → Fin m (or Fin n) sequence under the genuine product law, with positive sample size; reason: retains repetitions and the original empirical denominator; division by sample size presupposes positivity
--   - encoding: with probability at least 1 minus delta, simultaneously → ordinary product probability of the measurable failure set is at most delta; reason: equivalent complementary-event formulation, with all indicated pairs or hypotheses inside one event
--   - encoding: binary class of finite VC dimension d → Bool-valued functions, a set-valued H, and UnderstandingML.vcDim H = (d : Nat-infinity), including d=0; reason: same labelings and shattering; no finite-class restriction
--   - encoding: eta is the conditional probability of label 1 and h-star is its displayed Bayes rule → a measurable [0,1]-valued regression version satisfying the joint integral identity, with Bayes prediction true at eta=1/2; reason: binary Radon–Nikodym representation works on arbitrary measurable X and ties eta to D
--   - reading: the displayed p/q and mp/d are undefined for q=0 or d=0 → dL term is zero for d=0, and is d L(mp/d) for d>0 and q=0; reason: finite-cap extended-ratio convention preserves all defined cases and retains f=g, empty regions, and singleton classes
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Lemma 3, p. 6 (PDF p. 6)

import Definitions.Def_TsybakovLearning_OptimalERM_UniformBernstein

open MeasureTheory
universe uLemmaThree

namespace TsybakovLearning.OptimalERM

/-- Lemma 3, p. 6, including γ=1. The existential constant is shared with the complete
universal Lemma 2 property. No concentration premise enters the goal theorem. -/
theorem lemma_3 : ∃ c₀ : ℝ, 0 < c₀ ∧ UniformBernstein.{uLemmaThree} c₀ ∧
    ∀ (X : Type uLemmaThree) [MeasurableSpace X] (H : Set (X → Bool))
      (D : Measure (X × Bool)) [IsProbabilityMeasure D] (R : Regression D),
      MeasurableClass H D → ∀ d : ℕ, UnderstandingML.vcDim H = (d : ℕ∞) →
      ∀ a α : ℝ, 1 ≤ a → 0 < α → α < 1 → Tsybakov H D R a α →
      ∀ m : ℕ, 0 < m → ∀ γ δ : ℝ, 0 < γ → γ ≤ 1 → 0 < δ → δ < 1 →
      (∀ t : ℝ, MeasurableSet (smallExcessTail H D R γ m t)) →
        UnderstandingML.iidLaw D m (smallExcessFailure c₀ H D R a α γ δ d m) ≤
          ENNReal.ofReal δ := by sorry

end TsybakovLearning.OptimalERM
