-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_5_10
-- name    : PrivateUniformGen.Characterization.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:27.696336+00:00
-- url     : https://prove2.me/theorems/ed0e31b2-91cf-41bd-b873-6ba25b3ed9d0
-- title:
--   Lemma 5.10 — The middle robust-closure case is infinite
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   Assume $0\le\operatorname{CDim}(C)<\infty$ and $\operatorname{NBDim}(C)<\infty$, and fix the public integer $m>\operatorname{CDim}(C)$. Let $S\in X^n$ be arbitrary, allowing repeated entries, and $0\le t<N(C,m)$. If $R_t(S)$ is nonempty and
--
--   $$|\widehat S|-h_{\mathrm{fin}}(C)t>\operatorname{CDim}(C),$$
--
--   then $Q_t(S)\in C^\cap_\infty$. Thus the middle case of the robust closure definition is a valid infinite-intersection label.
--
--   Differences from the source:
--   - encoding: standing assumptions at the beginning of Section 5 → explicit nonnegative finite closure dimension and finite nested branching dimension; reason: these assumptions apply throughout the source section and are made visible in the theorem binders
--   - encoding: integer t in the public range and cardinality differences → natural t and m with t < N(C,m), with cardinality subtraction in the integers; reason: nonnegative source indices and positive public thresholds are unchanged; repetitions affect distinct support rather than input length
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 5.10, p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Robust

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_5_10 {X : Type} [Countable X] (C : LanguageClass X)
    (hc0 : 0 ≤ closureDim C) (hcf : closureDim C < ⊤) (hdf : nbDim C ⊤ < ⊤)
    (m : ℕ) (hm : (m : WithTop ℤ) > closureDim C)
    {n : ℕ} (S : Fin n → X) (t : ℕ) (ht : t < robustLength C m)
    (hcount : (((support S).card : ℤ) - (hellyNat C : ℤ) * t : WithTop ℤ) > closureDim C)
    (hR : (retained C S t).Nonempty) :
  robustClosure C S t ∈ infiniteClosure C := by sorry

end PrivateUniformGen.Characterization
