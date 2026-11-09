-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_5_11
-- name    : PrivateUniformGen.Characterization.lemma_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:52.7666+00:00
-- url     : https://prove2.me/theorems/1343f8fa-1b90-430e-b0e6-7a778f21dde0
-- title:
--   Lemma 5.11 — Robust closures nest and interlace
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   Under the finite, nonnegative closure-dimension and finite branching-dimension assumptions of Section 5, fix $m>\operatorname{CDim}(C)$. For two length-$n$ datasets $S,S'$ differing in at most one entry, and every $t$ with $t+1<N(C,m)$,
--
--   $$Q_{t+1}(S)\subseteq Q_t(S'),\qquad Q_{t+1}(S')\subseteq Q_t(S).$$
--
--   For every dataset $T$ of that length the whole chain is nested: $Q_j(T)\subseteq Q_i(T)$ whenever $0\le i\le j<N(C,m)$. This includes equal neighboring inputs and supports with repetitions.
--
--   Differences from the source:
--   - encoding: standing assumptions at the beginning of Section 5 → explicit nonnegative finite closure dimension and finite nested branching dimension; reason: these assumptions apply throughout the source section and are made visible in the theorem binders
--   - encoding: integer t in the public range and cardinality differences → natural t and m with t < N(C,m), with cardinality subtraction in the integers; reason: nonnegative source indices and positive public thresholds are unchanged; repetitions affect distinct support rather than input length
--   - encoding: the displayed descending chain → inclusion for every pair of indices i ≤ j in the public range; reason: this is exactly the transitive content of the same chain
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 5.11, p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Robust

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_5_11 {X : Type} [Countable X] (C : LanguageClass X)
    (hc0 : 0 ≤ closureDim C) (hcf : closureDim C < ⊤) (hdf : nbDim C ⊤ < ⊤)
    (m : ℕ) (hm : (m : WithTop ℤ) > closureDim C)
    {n : ℕ} (S S' : Fin n → X) (hne : Near S S') :
  (∀ t : ℕ, t + 1 < robustLength C m →
    robustClosure C S (t + 1) ⊆ robustClosure C S' t ∧
    robustClosure C S' (t + 1) ⊆ robustClosure C S t) ∧
  (∀ (T : Fin n → X) (i j : ℕ), i ≤ j → j < robustLength C m →
    robustClosure C T j ⊆ robustClosure C T i) := by sorry

end PrivateUniformGen.Characterization
