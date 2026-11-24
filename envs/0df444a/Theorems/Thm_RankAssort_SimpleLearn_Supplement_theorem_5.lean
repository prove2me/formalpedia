-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_Supplement_theorem_5
-- name    : RankAssort.SimpleLearn.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:26:21.760983+00:00
-- url     : https://prove2.me/theorems/b98dea13-f6af-4f60-b9fb-e57a4c95e24c
-- title:
--   Theorem 5 (corrected: general purchase law; proof's premise log₁₊α(n·rmax/ϵ) ≤ n; explicit count) — Algorithm 4 earns 1/(2 + α) of the optimal revenue minus ϵ w.p. 1 − δ
-- statement:
--   Work in the revenue model of §6: revenues $r_i\ge0$ with $r_{\max}=\max_i r_i$, customer types $\theta\sim\mathcal D$ with no bias, and a purchase law $\varphi_\theta$ ($\varphi\ge0$, $\sum_i\varphi_\theta(i)\le1$) for hooked customers; $\mathbb E[R(\pi)]$ is the expected revenue (4) of a (possibly partial) ranking $\pi$. Let $\epsilon,\delta,\alpha>0$ with $\epsilon/n\le r_{\max}$, and assume
--   $$\log_{1+\alpha}(n\,r_{\max}/\epsilon)\le n .$$
--   In the learning phase fresh customers arrive i.i.d.; for each the algorithm sees whether her first click is the candidate product and, if so, the revenue of her purchase. Run the Threshold Acceptance Algorithm for Revenue Maximization (Algorithm 4) with $\tau^{\max}=r_{\max}$, $\tau^{\min}=\epsilon/n$, an arbitrary scan order, and $L=\lceil (n^2r_{\max}^2/\epsilon^2)\log(n/\sqrt\delta)\rceil$ customers per display. Then:
--
--   1. on every realization, the learning phase uses at most
--   $$\big(1+\lfloor\log_{1+\alpha}(n\,r_{\max}/\epsilon)\rfloor\big)\cdot n\cdot L$$
--   customers, which gives the printed asymptotic order when the threshold logarithm and the unrounded sample size are both at least $1$;
--   2. with probability at least $1-\delta$, the returned ranking $\tilde\pi$ satisfies, for every ranking $\pi^*$ of the $n$ products,
--   $$\mathbb E[R(\tilde\pi)]\ \ge\ \frac1{2+\alpha}\,\mathbb E[R(\pi^*)]-\epsilon .$$
--
--   The threshold idea of Theorem 4 thus extends from hooking customers to the revenue they generate.
--
--   **Formalization Note** The run is `thresholdAcceptanceRev τ rev ϵ δ α order z` on `z s = Z s ω`; each customer is a type, a like-profile and a purchase outcome in `Fin (n + 1)`, with law `customerLawRev D τ φ`, measurable and mutually independent. The premise is the proof's own (p. 66: "as long as log1+α(rmax n/ϵ) ≤ n").
--
--   Differences from the source:
--   - correction: purchase probabilities φt(i, [n]) = exp(−νit/(ν0t + Σj νjt)) → any type-dependent purchase law φ θ i ≥ 0, measurable in θ, with Σᵢ φ θ i ≤ 1; reason: the printed formula is not a probability distribution (n = 2, ν ≡ 1: each φ = e^{−1/3} ≈ 0.72, sum > 1) while the proof needs Rt ∈ [0, rmax] (p. 65); both logit readings νᵢ/(ν₀ + Σν) and e^{νᵢ}/(e^{ν₀} + Σe^{ν}) are instances; every valid normalized logit instance is included; the printed unnormalized assignment is replaced
--   - correction: the statement has no condition linking α, ϵ, rmax and n → hypothesis log_{1+α}(n·rmax/ϵ) ≤ n; reason: added assumption taken from the proof (p. 66: 'as long as log1+α(rmax n/ϵ) ≤ n'), used to sum the per-threshold failure probabilities to δ; excluded cases: parameters with log_{1+α}(n·rmax/ϵ) > n
--   - correction: the length of the learning phase is O(r²max (n³/ϵ²) log1+α(n rmax/ϵ) log(n/√δ)) → on every realization the run uses at most (1 + ⌊log_{1+α}(n·rmax/ϵ)⌋)·n·L customers, L = ⌈(n² rmax²/ϵ²) log(n/√δ)⌉; reason: the printed O(·) omits an additive 1: when n·rmax = ϵ the logarithm is 0 but the first pass still uses up to n·L ≥ 1 customers (δ < 1); the explicit count is the one derived on p. 64, and it implies the printed O(·) when the threshold logarithm and the unrounded sample size are both at least 1; no case is excluded
--   - correction: per-unit revenue (or profit) ri → rᵢ ≥ 0; reason: the paper uses Rt(π) ∈ [0, rmax] (p. 42) and in the proof (p. 65); this excludes negative profits, which the analysis does not cover; this is a correction to the domain, not a consequence of the word profit
--   - encoding: bias fit(χ) = 0 (footnote 14) → hypothesis (τ θ).f ≡ 0 inside IsRevenueModel; reason: footnote 14's standing simplification of the revenue model, stated as a hypothesis on the published CustomerType
--   - reading: conditional upon getting hooked, the customer purchases product i with probability φt(i, [n]) → the purchase outcome is drawn from φ θ independently of the like-profile given θ; the algorithm observes the revenue of the purchase of customers whose first click is the candidate; reason: the purchase probability depends only on the type, not on which product was clicked (p. 40); Sir is 'the total revenue from customers whose first click is product i' (p. 42)
--   - encoding: products in U \ {i} are arbitrarily assigned to positions j > r → not modelled; reason: they do not affect the first click at rank r or the purchase, so the observations are the same for every such assignment
--   - encoding: τmax = rmax ≥ τmin = ϵ/n > 0 (Algorithm 4's input condition) → hypotheses 0 < ϵ, 0 < δ, 0 < α and ϵ/n ≤ rmax; reason: the input condition of Algorithm 4 at the theorem's parameters
--   - reading: π∗ the optimal ranking (optimal solution to OffAR) → every full ranking π∗ (duplicate-free, length n); reason: the optimum is attained among finitely many full rankings, so a bound against every full ranking is equivalent to the bound against the optimum; same reading as the published goal
--   - reading: for i ∈ U do (no order specified) → an arbitrary scan order (a permutation of the products), universally quantified; products accepted during a pass leave U at once and later products of the pass are tried at the next rank; reason: the page leaves the order free, so the theorem must hold for every order
--   - reading: returns a ranking π̃ (which may contain fewer than n products, p. 26) → the bound is stated for the returned, possibly partial, list itself; reason: the page says the remaining products may be appended 'without affecting the theoretical bounds'; appending products cannot decrease the expected hook (resp. revenue), so the bound for the returned list implies the one after appending
--   - encoding: the fraction of customers who only click on i, under the sequential click law with bias → each customer is a pair (θ, L) with θ ∼ D and like-profile L from the coupled first-click law (independent Bernoulli(pᵢ) coordinates); the algorithm observes the indicator noClickTop(σ ∪ i, r) ∧ clicksAt(σ ∪ i, r); reason: until her first click a customer clicks each product in her window with probability pᵢ + fᵢ(∅) = pᵢ (p. 53, published first_click_identity), so this indicator has exactly the law of the paper's 'clicks on the product at rank r without clicking on any of the previously ranked products' (p. 61); p. 28 notes the algorithms only use first clicks
--   - encoding: display a ranking to L customers (fresh arrivals, types i.i.d. from D) → a stream Z s, s ∈ ℕ, of measurable, mutually independent (iIndepFun) customers on an abstract probability space, each with the stated law; the run is a deterministic function of the realized stream, customers consumed in order; reason: the learning phase consumes fresh i.i.d. customers; the sanity file proves these hypotheses satisfiable (infinite product measure)
--   - encoding: L = (n² r²max/ϵ²) log(n/√δ) → ⌈(n² r²max/ϵ²) log(n/√δ)⌉ (Nat.ceil, natural logarithm); reason: a number of customers is a natural number; rounding up only enlarges the sample, and the count bound uses the same rounded L
--   - encoding: types drawn from an arbitrary distribution D → a probability measure D on a measurable type space Θ and a type map τ with TypeMeasurable τ; reason: as in every published base item: without measurability the expectations ∫ … ∂D would be junk zeros; the paper's expectations presuppose it
--   - encoding: with probability (1 − δ) → ENNReal.ofReal (1 − δ) ≤ P{ω | …}; reason: 'with probability 1 − δ' is read as 'at least 1 − δ', as in the published goal; ofReal makes the bound vacuous for δ ≥ 1
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 43, Theorem 5; p. 42, Algorithm 4; pp. 40–41, §6, (3)–(4), footnote 14; pp. 64–67, proof of Theorem 5 (count p. 64, premise p. 66)

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Threshold
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Revenue

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory ProbabilityTheory

/-- Theorem 5 (p. 43). In the revenue model of §6, customers `Z 0, Z 1, …` arrive i.i.d., each a
type `θ ∼ D` with a like-profile from the coupled first-click law and a purchase outcome from
`φ θ`. For every scan order, Algorithm 4 with `τmax = rmax`, `τmin = ϵ/n` and
`L = ⌈(n² rmax²/ϵ²) log(n/√δ)⌉`:
(1) on every realization consumes at most `(1 + ⌊log_{1+α}(n rmax/ϵ)⌋)·n·L` customers;
(2) with probability at least `1 − δ` returns a ranking `π̃` with
`E[R(π̃)] ≥ E[R(π∗)]/(2 + α) − ϵ` for every full ranking `π∗`.
The proof's premise `log_{1+α}(rmax n/ϵ) ≤ n` (p. 66) is a hypothesis. -/
theorem theorem_5 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) (hmodel : IsRevenueModel τ rev φ)
    (eps delta α : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) (hα : 0 < α)
    (heps_le : eps / n ≤ rmax rev)
    (hpremise : Real.logb (1 + α) (n * rmax rev / eps) ≤ n)
    (order : List (Fin n)) (horder : order.Perm (List.finRange n))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Θ × (Fin n → Bool) × Fin (n + 1)) (hZmeas : ∀ s, Measurable (Z s))
    (hZindep : iIndepFun Z P) (hZlaw : ∀ s, P.map (Z s) = customerLawRev D τ φ) :
    (∀ ω, (thresholdAcceptanceRev τ rev eps delta α order (fun s => Z s ω)).used ≤
        (1 + ⌊Real.logb (1 + α) (n * rmax rev / eps)⌋₊) * n *
          sampleSizeRev n eps delta (rmax rev)) ∧
      ENNReal.ofReal (1 - delta) ≤
        P {ω | ∀ piStar : List (Fin n), piStar.Nodup → piStar.length = n →
                1 / (2 + α) * expRevenue D τ rev φ piStar - eps ≤
                  expRevenue D τ rev φ
                    (thresholdAcceptanceRev τ rev eps delta α order (fun s => Z s ω)).ranked} := by sorry

end RankAssort.SimpleLearn.Supplement
