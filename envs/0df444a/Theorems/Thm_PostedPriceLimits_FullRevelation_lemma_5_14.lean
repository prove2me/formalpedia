-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_lemma_5_14
-- name    : PostedPriceLimits.FullRevelation.lemma_5_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:28.491256+00:00
-- url     : https://prove2.me/theorems/ace4cbfa-7acd-433d-a0d5-cc930fcd39df
-- title:
--   Lemma 5.14 — owner affordability forces non-owner stealing
-- statement:
--   In the construction of §5, for all sufficiently large $n$, consider any deterministic mechanism of the analysis model and a realisation of the randomness (every $\tau_t$ injective, $\pi$ a permutation, all labels in $[0,1]$) on which the good event $\mathcal E$ holds. Then for all relevant block-visit pairs $(t,i)$, with $p\in[0,\infty]^{Z_t}$ the prices posted on $Z_t$ at visit $i$,
--   $$W_t(p)\le5\,V_{t,i}(p)+\frac{\kappa|Z_t|}{n^2},$$
--   where $W_t(p)=\sum_{x\in Z_t}w_t(x)\mathbf 1(w_t(x)>p_x)$ is the owner value affordable at $p$ and $V_{t,i}(p)=w_t(S_{t,i}(p))$ is the owner value contained in the lexicographically smallest utility-maximizing set $S_{t,i}(p)$ of the non-owner valuation $v_{t,i}$.
--
--   Whatever owner value the prices make affordable, a non-owner visited earlier destroys a constant fraction of it; summed over visits this caps the owner welfare in Lemma 5.16.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: a realisation of the construction (τ_t injections, π a permutation, ξ ∈ [0,2], probabilities in [0,1]) → a latent point satisfying IsRealisation: every τ_t injective, π bijective, every uniform label in [0,1]; reason: the latent type also contains points outside the support of the law that are not realisations of the source's objects; the guard excludes exactly those
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Lemma 5.14, p.23 (PDF 24); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis

namespace PostedPriceLimits.FullRevelation

/-- Lemma 5.14 (for all sufficiently large `n`). For a genuine realisation on which `ℰ` holds, for every relevant
block-visit pair `(t, i)` with posted prices `p` on `Z_t`, `W_t(p) ≤ 5 V_{t,i}(p) + κ|Z_t|/n²`. -/
theorem lemma_5_14 : ∃ N : ℕ, ∀ n ≥ N, ∀ (M : AnalysisMech n) (ω : Latent n),
    IsRealisation ω → GoodEvent M ω → ∀ t i, IsRelevant ω t i →
      ownerAfford ω t (localPrice (M.postedPrice ω i) t) ≤
        5 * destroyed ω t i (localPrice (M.postedPrice ω i) t) + (kappa n : ℝ) * blockSize n / (n : ℝ) ^ 2 := by sorry

end PostedPriceLimits.FullRevelation
