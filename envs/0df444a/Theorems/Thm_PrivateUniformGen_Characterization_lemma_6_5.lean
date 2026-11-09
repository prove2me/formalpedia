-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_6_5
-- name    : PrivateUniformGen.Characterization.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:59.986101+00:00
-- url     : https://prove2.me/theorems/644aef84-8341-4193-9824-ed82ad82343e
-- title:
--   Lemma 6.5 — Private generation bounds the Helly number
-- statement:
--   Let $C$ be a language class on a countable space, and let $A$ be an $(\varepsilon,\delta)$-private uniform generator at a positive sample size $n$, with $\delta<1/n$. Then
--
--   $$h_{\mathrm{fin}}(C)\le n.$$
--
--   The privacy parameters are nonnegative, and the error may be zero. This bound applies to arbitrary, including uncountable, language classes and forces their Helly number to be finite.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
--   - encoding: sample size n with the expression 1/n → explicit 1 ≤ n; reason: uses the positive sample-size convention needed for the displayed reciprocal
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 6.5, p. 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Languages
import Definitions.Def_PrivateUniformGen_Characterization_Helly

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_6_5 {X : Type} [Countable X] (C : LanguageClass X)
    {n : ℕ} (hn : 1 ≤ n) (A : Mechanism X (Set X) n) (ε δ : ℝ)
    (hDP : IsDP A ε δ) (hgen : IsUniformGenerator C A) (hδ : δ < 1 / (n : ℝ)) :
  hellyNumber C.languages ≤ (n : ℕ∞) := by sorry

end PrivateUniformGen.Characterization
