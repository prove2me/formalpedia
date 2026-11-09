-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_6_10
-- name    : PrivateUniformGen.Characterization.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:20.505002+00:00
-- url     : https://prove2.me/theorems/873cc0dc-eb1c-4096-a38e-8b4790d7107b
-- title:
--   Lemma 6.10 — Binary trees obstruct private generation
-- statement:
--   There is an absolute constant $a>0$ such that for every language class $C$ on a countable space, every $n\ge2$, and every $(\varepsilon,\delta)$-private uniform generator $A$ with $0\le\varepsilon\le1$ and $\delta\le1/(12n)$, the existence of a binary nested branching tree of depth $d$ gives
--
--   $$n\ge a\log^*d.$$
--
--   Privacy includes nonnegative error and holds on every input. Tree depth counts nodes and is positive whenever such a tree exists. This bounds all available binary depths using the same constant.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: absolute constants in O and Omega → a positive real constant existentially quantified before all types, classes, privacy parameters, sample sizes and mechanisms; reason: makes the uniformity of the asymptotic notation explicit, with integer thresholds rounded upward by their comparison to the real bound
--   - encoding: binary nested branching tree of depth d → existence of a label K with HasTree C 2 d K; reason: the inductive tree encoding preserves exactly the source tree depths and arity bounds
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 6.10, p. 25. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_6_10  :
  ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [Countable X] (C : LanguageClass X)
    (n : ℕ), 2 ≤ n → ∀ (A : Mechanism X (Set X) n) (ε δ : ℝ),
    0 ≤ ε → ε ≤ 1 → δ ≤ 1 / (12 * (n : ℝ)) →
    IsDP A ε δ → IsUniformGenerator C A →
    ∀ d : ℕ, (∃ K : Set X, HasTree C 2 d K) →
      c * (logStar d : ℝ) ≤ (n : ℝ) := by sorry

end PrivateUniformGen.Characterization
