-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_5_8
-- name    : PrivateUniformGen.Characterization.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:02:04.830322+00:00
-- url     : https://prove2.me/theorems/741a69bf-1f02-40c0-a477-2f2ed09cf465
-- title:
--   Lemma 5.8 — Equal nested profiles have equal iterated cores
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   Under the standing conditions $0\le\operatorname{CDim}(C)<\infty$ and $\operatorname{NBDim}(C)<\infty$, let $H,K\in C^\cap_\infty$ satisfy $H\subseteq K$ and have equal profiles. Then
--
--   $$\operatorname{core}^*(H)=\operatorname{core}^*(K).$$
--
--   Equality identifies the actual terminal subsets of the example space. This provides a common output within a profile block.
--
--   Differences from the source:
--   - encoding: standing assumptions at the beginning of Section 5 → explicit nonnegative finite closure dimension and finite nested branching dimension; reason: these assumptions apply throughout the source section and are made visible in the theorem binders
--   - encoding: recursive profiles and iterated cores → lists and recursion with initial fuel equal to the finite rank; reason: every nonterminal step strictly reduces positive rank, so fuel does not truncate any source profile; the terminal output is the core
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 5.8, p. 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Profiles

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_5_8 {X : Type} [Countable X] (C : LanguageClass X)
    (hc0 : 0 ≤ closureDim C) (hcf : closureDim C < ⊤) (hdf : nbDim C ⊤ < ⊤)
    (H K : Set X) (hH : H ∈ infiniteClosure C) (hK : K ∈ infiniteClosure C)
    (hsub : H ⊆ K) (heq : profile C H = profile C K) :
  coreStar C H = coreStar C K := by sorry

end PrivateUniformGen.Characterization
