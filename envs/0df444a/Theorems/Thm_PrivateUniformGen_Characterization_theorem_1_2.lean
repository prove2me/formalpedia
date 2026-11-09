-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_theorem_1_2
-- name    : PrivateUniformGen.Characterization.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:12:25.808662+00:00
-- url     : https://prove2.me/theorems/0a574467-c642-47e1-a232-639fcd01701b
-- title:
--   Theorem 1.2 — Quantitative private generation upper bound
-- statement:
--   There is an absolute constant $a>0$ such that the following holds for every language class $C$ over every countable space. Suppose $c=\operatorname{CDim}(C)<\infty$ and $d=\operatorname{NBDim}(C)<\infty$, allowing $c=-1$. For every $\varepsilon,\delta\in(0,1)$ and every integer
--
--   $$n\ge c+1+a\frac{d2^d}{\varepsilon}\left(d+\log_2\frac1{\varepsilon\delta}\right),$$
--
--   there exists an $(\varepsilon,\delta)$-private uniform generator with sample size $n$. Privacy holds on all datasets; utility holds almost surely on every sequence of $n$ distinct examples from any target language, with an infinite output excluding the input. This states the paper's sample bound without fixing the hidden constant.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
--   - encoding: absolute constants in O and Omega → a positive real constant existentially quantified before all types, classes, privacy parameters, sample sizes and mechanisms; reason: makes the uniformity of the asymptotic notation explicit, with integer thresholds rounded upward by their comparison to the real bound
--   - generalization: a generator using the stated number of distinct examples → a generator at every integer input length above the threshold; reason: Theorem 5.16 supplies every input length and Theorem 5.17 preserves it; taking the least eligible integer recovers the source sample complexity
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Theorem 1.2, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem theorem_1_2  :
  ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [Countable X] (C : LanguageClass X),
    closureDim C < ⊤ → nbDim C ⊤ < ⊤ →
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ n : ℕ, (cdimInt C : ℝ) + 1 + c * generationScale C ε δ ≤ (n : ℝ) →
      ∃ A : Mechanism X (Set X) n, IsDP A ε δ ∧ IsUniformGenerator C A := by sorry

end PrivateUniformGen.Characterization
