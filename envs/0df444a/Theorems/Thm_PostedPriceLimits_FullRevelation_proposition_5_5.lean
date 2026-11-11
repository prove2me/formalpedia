-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_proposition_5_5
-- name    : PostedPriceLimits.FullRevelation.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:34.247066+00:00
-- url     : https://prove2.me/theorems/cdfdd63b-546c-4583-bb22-5cdd5e22a864
-- title:
--   Proposition 5.5 — the utility-maximizing clause uses visited names and approximates $\Pi B_{t,p}$
-- statement:
--   In the construction of §5, for all sufficiently large $n$, consider any deterministic mechanism of the analysis model and a realisation of the randomness (every $\tau_t$ injective, $\pi$ a permutation, all labels in $[0,1]$) on which the good event $\mathcal E$ holds. Let $(t,i)$ be a relevant block-visit pair, let $p\in[0,\infty]^{Z_t}$ be the prices the mechanism posts on $Z_t$ at visit $i$, and suppose $W_t(p)\ge|Z_t|$, where $W_t(p)=\sum_{x\in Z_t}w_t(x)\mathbf 1(w_t(x)>p_x)$. Let $\gamma^*=(\tau_t(i),L^*)$ and $A^*:[\kappa]\times Z_t\to\{0,\varepsilon,\dots,1\}$ define a utility-maximizing clause for $v_{t,i}$ at $p$ (that is, $\gamma^*\in\Gamma_{t,i}$, $A^*\in\mathcal A_{t,\gamma^*}$, and $U_t(\gamma^*,A^*,p)$ is maximal among the clauses of $v_{t,i}$). Then:
--   1. $L^*\subseteq\tau_t([i])$;
--   2. $\mathrm{Avg}\big[(A^*-\Pi_{t,\tau_t([i-1])}B_{t,p})^2\big]\le8\varepsilon n$.
--
--   Utility maximization therefore makes the non-owner choose a clause built from names already revealed, whose grid function tracks the affordability profile $B_{t,p}$ as seen through the information available before visit $i$.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: a realisation of the construction (τ_t injections, π a permutation, ξ ∈ [0,2], probabilities in [0,1]) → a latent point satisfying IsRealisation: every τ_t injective, π bijective, every uniform label in [0,1]; reason: the latent type also contains points outside the support of the law that are not realisations of the source's objects; the guard excludes exactly those
--   - encoding: γ*, A* define a utility-maximizing clause for v_{t,i} → γ* ∈ Γ_{t,i}, A* ∈ 𝒜_{t,γ*} and U_t(γ*,A*,p) ≥ U_t(γ,A,p) for all clauses of v_{t,i}; reason: v_{t,i}(S) − p(S) is maximized over S and clauses jointly; a clause is utility-maximizing iff it attains the maximal normalized utility
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition 5.5, p.19 (PDF 20); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis

namespace PostedPriceLimits.FullRevelation

/-- Proposition 5.5 (for all sufficiently large `n`). For a genuine realisation on which `ℰ` holds and `W_t(p) ≥ |Z_t|`,
where `(t, i)` is a relevant block-visit pair and `p` the prices posted on `Z_t` at visit `i`.
If `γ* = (τ_t(i), L*)` and `A*` define a utility-maximizing clause of `v_{t,i}`, then
(1) `L* ⊆ τ_t([i])` and (2) `Avg[(A* − Π_{t,τ_t([i−1])} B_{t,p})²] ≤ 8εn`. -/
theorem proposition_5_5 : ∃ N : ℕ, ∀ n ≥ N, ∀ (M : AnalysisMech n) (ω : Latent n),
    IsRealisation ω → GoodEvent M ω → ∀ t i, IsRelevant ω t i →
      (blockSize n : ℝ) ≤ ownerAfford ω t (localPrice (M.postedPrice ω i) t) →
      ∀ (γ : Ctx n) (A : ℕ → Fin (blockSize n) → ℝ), IsUtilMaxClause ω t i (localPrice (M.postedPrice ω i) t) γ A →
        γ.1.2 ⊆ (upTo i).image (names ω t) ∧
        avgRK n (fun k x => (A k x -
          proj ω t ((before i).image (names ω t)) (affordFn n (localPrice (M.postedPrice ω i) t)) k x) ^ 2) ≤
            8 * eps n * n := by sorry

end PostedPriceLimits.FullRevelation
