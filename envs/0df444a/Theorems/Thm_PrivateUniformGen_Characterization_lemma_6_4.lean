-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_6_4
-- name    : PrivateUniformGen.Characterization.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:35.895707+00:00
-- url     : https://prove2.me/theorems/1c004808-e0fd-46d8-88d8-62fcfe9614f6
-- title:
--   Lemma 6.4 — Interior-point impossibility on some finite domain
-- statement:
--   Fix $n\ge1$, a finite real $\varepsilon\ge0$, and $0\le\delta<1/n$. There exist $N\ge2$ and $\eta>0$ such that every $(\varepsilon,\delta)$-private randomized mechanism $M:[N]^n\to[N]$ has an input $y$ with
--
--   $$\Pr[\min_i y_i\le M(y)\le\max_i y_i]<1-\eta.$$
--
--   The domain and the positive gap are chosen before the mechanism. The source attributes this obstruction to BNSV15, using its fingerprinting results in Appendix B; no code or tracing theorem is an assumption here.
--
--   Differences from the source:
--   - encoding: the ordered domain [N] = {1,...,N} → Fin N = {0,...,N-1}, with interior event expressed by a lower and an upper input witness; reason: translation by one preserves order, neighboring inputs and all event probabilities; positive sample sizes make the witness event exactly the min/max event
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 6.4, p. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_6_4 (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / (n : ℝ)) :
  ∃ N : ℕ, 2 ≤ N ∧ ∃ η : ℝ, 0 < η ∧
    ∀ M : Mechanism (Fin N) (Fin N) n, IsDP M ε δ →
      ∃ y : Fin n → Fin N, (M y : Measure (Fin N)).real (InteriorEvent y) < 1 - η := by sorry

end PrivateUniformGen.Characterization
