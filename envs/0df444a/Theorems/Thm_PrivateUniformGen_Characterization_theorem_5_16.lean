-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_theorem_5_16
-- name    : PrivateUniformGen.Characterization.theorem_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:13:16.492462+00:00
-- url     : https://prove2.me/theorems/002f5bc5-9cec-4b7e-9e0e-d203581aa549
-- title:
--   Theorem 5.16 — Private selection with exact and asymptotic thresholds
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   There is an absolute constant $a>0$ with the following property. Let $C$ satisfy $0\le c=\operatorname{CDim}(C)<\infty$ and $d=\operatorname{NBDim}(C)<\infty$, set $h=h_{\mathrm{fin}}(C)$, and let $\varepsilon,\delta\in(0,1)$. For every public integer
--
--   $$m\ge c+\frac{8h(2^d+1)}{\varepsilon}\max\left\{\ln\frac{2(2^d+1)}{\varepsilon},\ \ln\frac{2^d+1}{\delta}+\frac{\varepsilon}{4}\right\},$$
--
--   and every input length $n$, there is an $(\varepsilon,\delta)$-private mechanism on all of $X^n$ with infinite output almost surely on every input. Whenever $\widehat S$ lies in a language and $|\widehat S|\ge m$, it satisfies
--
--   $$\Pr[|A(S)|=\infty\ \text{and}\ A(S)\subseteq\langle\widehat S\rangle_C]=1.$$
--
--   In particular, for every input length a mechanism with the same privacy and global infiniteness guarantees satisfies this utility at the sufficient threshold $c+a h2^d(d+\log_2(1/\varepsilon)+\log_2(1/\delta))/\varepsilon$. Natural logarithms occur in the exact threshold; base-two logarithms occur in the asymptotic bound. No novelty guarantee is imposed at this selection stage.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
--   - encoding: absolute constants in O and Omega → a positive real constant existentially quantified before all types, classes, privacy parameters, sample sizes and mechanisms; reason: makes the uniformity of the asymptotic notation explicit, with integer thresholds rounded upward by their comparison to the real bound
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Theorem 5.16, p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem theorem_5_16  :
  ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [Countable X] (C : LanguageClass X),
    0 ≤ closureDim C → closureDim C < ⊤ → nbDim C ⊤ < ⊤ →
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    (∀ m : ℕ, selectionThreshold C ε δ ≤ (m : ℝ) →
      ∀ n : ℕ, ∃ A : Mechanism X (Set X) n,
        IsDP A ε δ ∧ InfiniteEveryInput A ∧ SelectionUtility C A m) ∧
    (∀ n : ℕ, ∃ A : Mechanism X (Set X) n,
      IsDP A ε δ ∧ InfiniteEveryInput A ∧
      SelectionUtility C A ((cdimInt C : ℝ) + c * selectionScale C ε δ)) := by sorry

end PrivateUniformGen.Characterization
