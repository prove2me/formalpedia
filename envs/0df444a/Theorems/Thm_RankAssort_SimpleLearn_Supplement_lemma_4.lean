-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_Supplement_lemma_4
-- name    : RankAssort.SimpleLearn.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:25:49.797793+00:00
-- url     : https://prove2.me/theorems/d455e083-63c6-4c35-97bb-9a226d1e2086
-- title:
--   Lemma 4 (corrected: general purchase law) — E[R(π∗)] ≤ E[R(π̃)] + Σᵣ E[Pr(C̄(r − 1, π̃) C_{π∗⁻¹(r)}(π∗) = 1)·Σᵢ rᵢφ(i)], for every π∗ and π̃
-- statement:
--   Work in the revenue model of §6: products $i\in[n]$ with revenues $r_i\ge0$; customer types $\theta\sim\mathcal D$ with click probabilities $p_i(\theta)$, window $k(\theta)$ and no bias; a hooked customer of type $\theta$ purchases $i$ with probability $\varphi_\theta(i)\ge0$, $\sum_i\varphi_\theta(i)\le1$. For a ranking $\pi$, $\mathbb E[R(\pi)]$ is the expected revenue (4), $\bar C(r,\pi)=1$ is the event that the customer clicks none of the top $r$ products of $\pi$, and $C_{\pi^{-1}(r)}(\pi)=1$ the event that she clicks the product at rank $r$. For every ranking $\pi^*$ of the $n$ products and every duplicate-free, possibly partial, ranking $\tilde\pi$,
--   $$\mathbb E[R(\pi^*)]\ \le\ \mathbb E[R(\tilde\pi)]+\sum_{r=1}^{n}\mathbb E_\theta\Big[\Pr\big(\bar C(r-1,\tilde\pi)\,C_{\pi^{*-1}(r)}(\pi^*)=1\big)\sum_{i\in[n]}r_i\varphi_\theta(i)\Big].$$
--
--   This is the revenue-weighted counterpart of (10) and the first step in the proof of Theorem 5, where $\tilde\pi$ is the ranking returned by Algorithm 4 and each term is then bounded by the threshold at that rank.
--
--   **Formalization Note** Ranks are 0-based: the term for the paper's rank $r$ is `revJointTerm D τ rev φ π̃ π∗ (r − 1)`, the probability taken under the coupled like-profile; with zero bias, clicks inside the window are independent likes, so this is the joint law of the clicks under $\tilde\pi$ and $\pi^*$. The hypothesis `IsRevenueModel τ rev φ` carries $f\equiv0$, $r_i\ge0$ and the purchase law.
--
--   Differences from the source:
--   - generalization: π∗ the optimum revenue maximizing ranking and π̃ the ranking returned by Algorithm 4 → every full ranking π∗ and every duplicate-free (possibly partial) ranking π̃; reason: the proof (pp. 67–68) uses neither optimality nor the algorithm; the source's pair is a special case
--   - correction: purchase probabilities φt(i, [n]) = exp(−νit/(ν0t + Σj νjt)) → any type-dependent purchase law φ θ i ≥ 0, measurable in θ, with Σᵢ φ θ i ≤ 1; reason: the printed formula is not a probability distribution (n = 2, ν ≡ 1: each φ = e^{−1/3} ≈ 0.72, sum > 1) while the paper uses Rt ∈ [0, rmax] (pp. 42, 65); both logit readings νᵢ/(ν₀ + Σν) and e^{νᵢ}/(e^{ν₀} + Σe^{ν}) are instances; every valid normalized logit instance is included; the printed unnormalized assignment is replaced
--   - correction: per-unit revenue (or profit) ri → rᵢ ≥ 0; reason: the paper uses Rt(π) ∈ [0, rmax] (p. 42) and in the proof of Theorem 5 (p. 65); this excludes negative profits, which the analysis does not cover; this is a correction to the domain, not a consequence of the word profit
--   - encoding: Pr(C̄t(r − 1, π̃) Cπ∗⁻¹(r)t(π∗) = 1) with zero bias (footnote 14) → coupledProb of noClickTop π̃ (r − 1) ∧ clicksAt π∗ (r − 1), with f ≡ 0 as a hypothesis; reason: with zero bias each product in the window is clicked independently with probability pᵢ, which is the coupled law; ranks 0-based
--   - encoding: types drawn from an arbitrary distribution D → a probability measure D on a measurable type space Θ and a type map τ with TypeMeasurable τ; reason: as in every published base item: without measurability the expectations ∫ … ∂D would be junk zeros; the paper's expectations presuppose it
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 67, Lemma 4 (proof pp. 67–68); pp. 40–41, §6, (3)–(4), footnote 14

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Threshold
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Revenue

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory

/-- Lemma 4 (p. 67). In the revenue model of §6 (zero bias, `rᵢ ≥ 0`, purchase law `φ`), for every
full ranking `π∗` and every (possibly partial) ranking `π̃`,
`E[R(π∗)] ≤ E[R(π̃)] + Σ_{r=1}^n E_t[Pr(C̄(r − 1, π̃) C_{π∗⁻¹(r)}(π∗) = 1) Σᵢ rᵢ φ_t(i)]`
(ranks 0-based in Lean). -/
theorem lemma_4 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) (hmodel : IsRevenueModel τ rev φ)
    (piT piStar : List (Fin n)) (hT : piT.Nodup) (hs : piStar.Nodup)
    (hslen : piStar.length = n) :
    expRevenue D τ rev φ piStar ≤
      expRevenue D τ rev φ piT + ∑ r ∈ Finset.range n, revJointTerm D τ rev φ piT piStar r := by sorry

end RankAssort.SimpleLearn.Supplement
