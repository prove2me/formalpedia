-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_Supplement_lemma_1
-- name    : PigeonholeDesign.Upper.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:00:18.218185+00:00
-- url     : https://prove2.me/theorems/9b67f4a5-826f-40fc-b555-76c580b6ca94
-- title:
--   Lemma 1 — on $[0,1]$ the matched-pair design has discrepancy at most 1
-- statement:
--   $T$ subjects arrive one at a time, $T$ even (p. 9). Subject $t$ carries a covariate $x_t\in\mathcal S=[0,1]^{p+q}$: $p$ continuous coordinates in $[0,1]$ and $q$ discrete coordinates, the $i$-th taking values in a finite support $S_i\subseteq[0,1]$ whose size does not depend on $T$ (pp. 10, 21). The sequence $x=(x_1,\dots,x_T)$ is chosen in advance by an adversary. For a split of the subjects into a control group $A$ and a treated group $B$ with $|A|=|B|$, the **discrepancy** $d_{A,B}$ is the minimum total Euclidean length of a perfect matching between $A$ and $B$ (display (1), p. 11).
--
--   The **matched-pair design** (Definition 1, p. 12) knows all covariates in advance and uses the best balanced split, so its discrepancy is
--   $$d^{\mathrm{MP}}(x)=\min_{|A|=|B|=T/2} d_{A,B};$$
--   randomly swapping the two subjects of each matched pair does not change it.
--
--   **Lemma 1 (p. 13).** Let $p=1$, $q=0$, so every covariate is a number in $[0,1]$. For every even $T$ and every arrival sequence $x\in[0,1]^T$,
--   $$d^{\mathrm{MP}}(x)\le 1 .$$
--
--   The bound does not grow with $T$: with full information one continuous covariate costs only a constant. Theorem 4 applies it on each discrete support.
--
--   **Formalization Note** Covariates are real numbers with the distance $|a-b|$, which is the Euclidean distance on $[0,1]^1$. `mpdDisc x` is the infimum of `discrepancy x w` over the splits with exactly $T/2$ control subjects.
--
--   Differences from the source:
--   - encoding: covariate space [0,1] (p = 1, q = 0) → x : Fin T → ℝ with every x t ∈ [0,1], distance |a − b|; subjects indexed from 0; reason: the Euclidean distance on [0,1]^1
--   - encoding: the matched-pair design's discrepancy d_{A*,B*} (Definition 1, display (2)) after the random swaps inside the pairs → mpdDisc x, the infimum of discrepancy x w over the splits with exactly T/2 control subjects; reason: the swaps keep the optimal matching feasible, so the discrepancy after them equals the minimum in (2)
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 13, Lemma 1 (proof: Appendix EC.3, p. ec3)

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

namespace PigeonholeDesign.Upper.Supplement

theorem lemma_1 (T : ℕ) (hT : Even T) (x : Fin T → ℝ) (hx : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1) :
    mpdDisc x ≤ 1 := by sorry

end PigeonholeDesign.Upper.Supplement
