-- Prove2me | Theorems.Thm_TsybakovLearning_OptimalERM_lemma_2
-- name    : TsybakovLearning.OptimalERM.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:31.318873+00:00
-- url     : https://prove2.me/theorems/2096fc8b-4c14-42ff-b24a-0072f74b68d9
-- title:
--   Lemma 2 — region-sensitive uniform Bernstein inequality
-- statement:
--   There is a universal numerical $c_0>0$ with the following property. Let $H\subseteq\{0,1\}^X$ be a measurable class with VC dimension $d<\infty$, let $D$ be any probability law on $X\times\{0,1\}$, and let $\Delta\subseteq X$ be any measurable region. For $m\ge1$, $0<\delta<1$, and $S\sim D^m$, with probability at least $1-\delta$ every pair $f,g\in H$ satisfies
--
--   $$\left|(\mathrm{er}_{D,\Delta}(f)-\mathrm{er}_{D,\Delta}(g))-(\widehat{\mathrm{er}}_{S,\Delta}(f)-\widehat{\mathrm{er}}_{S,\Delta}(g))\right|\le c_0\sqrt{\frac{qA}{m}}+\frac{c_0A}{m},$$
--   $$p=D_X(\Delta),\quad q=D_X(\{f\ne g\}\cap\Delta),\quad A=dL\!\left(\frac pq\wedge\frac{mp}d\right)+L(1/\delta),\qquad L(x)=\log_2(\max\{x,2\}).$$
--
--   The region mass stays in both logarithmic arguments. This uniform absolute-deviation inequality is the first milestone used by the Tsybakov concentration result.
--
--   **Formalization Note** The theorem asserts existence of the fully expanded universal Bernstein property. At $q=0,d>0$, use $dL(mp/d)$; at $d=0$ the $dL$ term is zero. This is the finite-cap limiting reading, not Lean division by zero. Restricted empirical quantities divide by m. The measurable-class convention includes signed empirical suprema of the localized centered and uncentered loss differences; every exact failure event is measurable for all coefficients.
--
--   Differences from the source:
--   - encoding: a universal positive numerical c0 → an existential c0 before every instance type and data with its full UniformBernstein property; reason: one witness works for every pair, region, dimension, distribution and confidence level
--   - reading: measurable class and ordinary probability convention → measurable hypotheses, measurable finite signed empirical suprema for the restricted localized and centered loss-difference classes, and measurable exact failure or tail events for all thresholds; reason: makes Lemma 2 and Appendix A measurability explicit without countability, pointwise separability, topology, a measurable ERM selection, or any probability estimate
--   - encoding: an i.i.d. sample written with braces → Fin m (or Fin n) sequence under the genuine product law, with positive sample size; reason: retains repetitions and the original empirical denominator; division by sample size presupposes positivity
--   - encoding: with probability at least 1 minus delta, simultaneously → ordinary product probability of the measurable failure set is at most delta; reason: equivalent complementary-event formulation, with all indicated pairs or hypotheses inside one event
--   - encoding: binary class of finite VC dimension d → Bool-valued functions, a set-valued H, and UnderstandingML.vcDim H = (d : Nat-infinity), including d=0; reason: same labelings and shattering; no finite-class restriction
--   - reading: the displayed p/q and mp/d are undefined for q=0 or d=0 → dL term is zero for d=0, and is d L(mp/d) for d>0 and q=0; reason: finite-cap extended-ratio convention preserves all defined cases and retains f=g, empty regions, and singleton classes
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), Lemma 2, pp. 5–6 (PDF pp. 5–6)

import Definitions.Def_TsybakovLearning_OptimalERM_UniformBernstein

open MeasureTheory
universe uLemmaTwo

namespace TsybakovLearning.OptimalERM

/-- Lemma 2, pp. 5–6. One numerical constant, before all types and data. -/
theorem lemma_2 : ∃ c₀ : ℝ, 0 < c₀ ∧ UniformBernstein.{uLemmaTwo} c₀ := by sorry

end TsybakovLearning.OptimalERM
