-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_6_9
-- name    : PrivateUniformGen.Characterization.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:15:32.438722+00:00
-- url     : https://prove2.me/theorems/e6c14918-290b-40d0-9df8-24a2d98b94c9
-- title:
--   Lemma 6.9 — Quantitative interior-point lower bound
-- statement:
--   There is an absolute constant $a>0$ such that for all $m\ge1$, $N\ge2$, $0\le\varepsilon\le1$ and $0\le\delta\le1/(12(m+1))$, every $(\varepsilon,\delta)$-private randomized mechanism $M:[N]^m\to[N]$ satisfying
--
--   $$\Pr[\min_i y_i\le M(y)\le\max_i y_i]\ge\frac23\qquad\text{for every }y\in[N]^m$$
--
--   obeys $m\ge a\log^*N$, with base-two iterated logarithm. The constant is independent of the domain, sample size, privacy parameters and mechanism. Appendix B derives this result from BNSV15.
--
--   Differences from the source:
--   - encoding: the ordered domain [N] = {1,...,N} → Fin N = {0,...,N-1}, with interior event expressed by a lower and an upper input witness; reason: translation by one preserves order, neighboring inputs and all event probabilities; positive sample sizes make the witness event exactly the min/max event
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: absolute constants in O and Omega → a positive real constant existentially quantified before all types, classes, privacy parameters, sample sizes and mechanisms; reason: makes the uniformity of the asymptotic notation explicit, with integer thresholds rounded upward by their comparison to the real bound
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 6.9, p. 24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_6_9  :
  ∃ c : ℝ, 0 < c ∧ ∀ m N : ℕ, 1 ≤ m → 2 ≤ N →
    ∀ ε δ : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 / (12 * ((m : ℝ) + 1)) →
    ∀ M : Mechanism (Fin N) (Fin N) m, IsDP M ε δ →
      (∀ y : Fin m → Fin N, (2 : ℝ) / 3 ≤
        (M y : Measure (Fin N)).real (InteriorEvent y)) →
      c * (logStar N : ℝ) ≤ (m : ℝ) := by sorry

end PrivateUniformGen.Characterization
