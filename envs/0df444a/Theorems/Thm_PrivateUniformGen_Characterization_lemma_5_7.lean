-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_5_7
-- name    : PrivateUniformGen.Characterization.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:02:09.871496+00:00
-- url     : https://prove2.me/theorems/f42e2fe6-e13a-494e-aa46-48a7e096f4f2
-- title:
--   Lemma 5.7 — Profiles are monotone under inclusion
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   Assume the standing conditions of Section 5: $0\le\operatorname{CDim}(C)<\infty$ and $\operatorname{NBDim}(C)<\infty$. For $H,K\in C^\cap_\infty$ with $H\subseteq K$,
--
--   $$\operatorname{profile}(K)\preceq_{\operatorname{NBDim}(C)}\operatorname{profile}(H).$$
--
--   The order is the recursive order on decreasing rank sequences, including its reversed tail comparison. This is the monotonicity needed to define contiguous profile blocks.
--
--   Differences from the source:
--   - encoding: standing assumptions at the beginning of Section 5 → explicit nonnegative finite closure dimension and finite nested branching dimension; reason: these assumptions apply throughout the source section and are made visible in the theorem binders
--   - encoding: recursive profiles and iterated cores → lists and recursion with initial fuel equal to the finite rank; reason: every nonterminal step strictly reduces positive rank, so fuel does not truncate any source profile; the terminal output is the core
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 5.7, p. 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Profiles

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_5_7 {X : Type} [Countable X] (C : LanguageClass X)
    (hc0 : 0 ≤ closureDim C) (hcf : closureDim C < ⊤) (hdf : nbDim C ⊤ < ⊤)
    (H K : Set X) (hH : H ∈ infiniteClosure C) (hK : K ∈ infiniteClosure C)
    (hsub : H ⊆ K) :
  profileLE (nbDim C ⊤).toNat (profile C K) (profile C H) := by sorry

end PrivateUniformGen.Characterization
