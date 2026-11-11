-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_proposition_5_10
-- name    : PostedPriceLimits.FullRevelation.proposition_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:28.04098+00:00
-- url     : https://prove2.me/theorems/16453a42-f74f-4088-8d48-cdeb27ad5ca8
-- title:
--   Proposition 5.10 — uniform affordability within rank intervals
-- statement:
--   In the construction of §5, for all sufficiently large $n$, consider any deterministic mechanism of the analysis model and a realisation of the randomness (every $\tau_t$ injective, $\pi$ a permutation, all labels in $[0,1]$) on which the good event $\mathcal E$ holds. Let $(t,i)$ be a relevant block-visit pair, let $p\in[0,\infty]^{Z_t}$ be the prices the mechanism posts on $Z_t$ at visit $i$, and suppose $W_t(p)\ge|Z_t|$, where $W_t(p)=\sum_{x\in Z_t}w_t(x)\mathbf 1(w_t(x)>p_x)$. Let $\gamma^*=(\tau_t(i),L^*)$ and $A^*:[\kappa]\times Z_t\to\{0,\varepsilon,\dots,1\}$ define a utility-maximizing clause for $v_{t,i}$ at $p$ (that is, $\gamma^*\in\Gamma_{t,i}$, $A^*\in\mathcal A_{t,\gamma^*}$, and $U_t(\gamma^*,A^*,p)$ is maximal among the clauses of $v_{t,i}$). Then for all $k,r,r'\in[\kappa]$ with $\mathcal K_{|\gamma^*|-1}(r)=\mathcal K_{|\gamma^*|-1}(r')$,
--   $$\big|\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r}]-\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r'}]\big|\le\lambda^{-2}.$$
--
--   Owner ranks that the mechanism cannot yet distinguish receive essentially the same affordability; this is the balance property that lets non-owners steal in Lemma 5.14.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: a realisation of the construction (τ_t injections, π a permutation, ξ ∈ [0,2], probabilities in [0,1]) → a latent point satisfying IsRealisation: every τ_t injective, π bijective, every uniform label in [0,1]; reason: the latent type also contains points outside the support of the law that are not realisations of the source's objects; the guard excludes exactly those
--   - encoding: γ*, A* define a utility-maximizing clause → γ* ∈ Γ_{t,i}, A* ∈ 𝒜_{t,γ*} and U_t(γ*,A*,p) ≥ U_t(γ,A,p) for all clauses of v_{t,i}; reason: a clause is utility-maximizing iff it attains the maximal normalized utility
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition 5.10, p.22 (PDF 23); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis

namespace PostedPriceLimits.FullRevelation

/-- Proposition 5.10 (for all sufficiently large `n`). Under the hypotheses of Proposition 5.5,
for all `k, r, r' ∈ [κ]` with `𝒦_{|γ*|−1}(r) = 𝒦_{|γ*|−1}(r')`,
`|Avg[B_{t,p}(k, ·) | Z_{t,r}] − Avg[B_{t,p}(k, ·) | Z_{t,r'}]| ≤ λ^{−2}`. -/
theorem proposition_5_10 : ∃ N : ℕ, ∀ n ≥ N, ∀ (M : AnalysisMech n) (ω : Latent n),
    IsRealisation ω → GoodEvent M ω → ∀ t i, IsRelevant ω t i →
      (blockSize n : ℝ) ≤ ownerAfford ω t (localPrice (M.postedPrice ω i) t) →
      ∀ (γ : Ctx n) (A : ℕ → Fin (blockSize n) → ℝ), IsUtilMaxClause ω t i (localPrice (M.postedPrice ω i) t) γ A →
        ∀ k ∈ rankRange (kappa n), ∀ r ∈ rankRange (kappa n), ∀ r' ∈ rankRange (kappa n),
          partOf (rankPartition (kappa n) (γ.1.2.card - 1)) r =
            partOf (rankPartition (kappa n) (γ.1.2.card - 1)) r' →
          |avg (ownerRankSet ω t r) (affordFn n (localPrice (M.postedPrice ω i) t) k) -
            avg (ownerRankSet ω t r') (affordFn n (localPrice (M.postedPrice ω i) t) k)| ≤ ((lam n : ℝ) ^ 2)⁻¹ := by sorry

end PostedPriceLimits.FullRevelation
