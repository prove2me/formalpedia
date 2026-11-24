-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_Supplement_theorem_4
-- name    : RankAssort.SimpleLearn.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:25:18.734694+00:00
-- url     : https://prove2.me/theorems/a91fb403-5bf4-42f9-b27e-7286b272b7a3
-- title:
--   Theorem 4 (corrected: proof's premise log₁₊α(n/ϵ) ≤ n; explicit learning-phase count) — Threshold Acceptance hooks 1/(2 + α) of the optimum minus ϵ w.p. 1 − δ
-- statement:
--   Customer types are drawn i.i.d. from $\mathcal D$; $\mathbb E[H(\pi)]$ is the probability that a customer is hooked by the (possibly partial) ranking $\pi$. Let $\epsilon,\delta,\alpha>0$ with $\epsilon/n\le1$, and assume
--   $$\log_{1+\alpha}(n/\epsilon)\le n .$$
--   In the learning phase, fresh customers arrive i.i.d.; the algorithm sees only whether each customer clicks the candidate product and nothing ranked before it. Run the Threshold Acceptance Algorithm (Algorithm 3) with $\tau^{\max}=1$, $\tau^{\min}=\epsilon/n$, an arbitrary scan order of the products, and $L=\lceil (n^2/\epsilon^2)\log(n/\sqrt\delta)\rceil$ customers per display. Then:
--
--   1. on every realization, the learning phase uses at most
--   $$\big(1+\lfloor\log_{1+\alpha}(n/\epsilon)\rfloor\big)\cdot n\cdot L$$
--   customers, which gives the printed asymptotic order when $\log_{1+\alpha}(n/\epsilon)\ge1$ and the unrounded sample size is at least $1$;
--   2. with probability at least $1-\delta$, the returned ranking $\tilde\pi$ satisfies, for every ranking $\pi^*$ of the $n$ products,
--   $$\mathbb E[H(\tilde\pi)]\ \ge\ \frac{1}{2+\alpha}\,\mathbb E[H(\pi^*)]-\epsilon .$$
--
--   Compared with the Simple Learning Algorithm, which needs $\Theta(n^4)$ customers, the threshold rule trades a slightly worse ratio $1/(2+\alpha)$ for a learning phase of order $n^3\log n$.
--
--   **Formalization Note** The run is `thresholdAcceptance τ ϵ δ α order z` on the realized stream `z s = Z s ω`; `.ranked` is $\tilde\pi$ and `.used` the number of customers consumed. The customers `Z s` are measurable, mutually independent and each has law `customerLaw D τ`. The premise $\log_{1+\alpha}(n/\epsilon)\le n$ is the proof's own assumption (p. 60). The union bound (33) counts $\log_{1+\alpha}(n/\epsilon)$ threshold values while footnote 18 counts $a+1$ of them, $a=\log_{1+\alpha}(n/\epsilon)$; the premise is kept as printed.
--
--   Differences from the source:
--   - correction: the statement has no condition linking α, ϵ and n → hypothesis log_{1+α}(n/ϵ) ≤ n; reason: added assumption taken from the proof (p. 60: 'we will also implicitly assume that the parameters α, ϵ, δ are chosen such that n ≥ log1+α(n/ϵ)'), which the union bound (33) uses to sum the per-threshold failure probabilities δ/n to δ; excluded cases: parameters with log_{1+α}(n/ϵ) > n, where the paper says to run Algorithm 2 instead
--   - correction: the length of the learning phase is O((n³/ϵ²) log1+α(n/ϵ) log(n/√δ)) → on every realization the run uses at most (1 + ⌊log_{1+α}(n/ϵ)⌋)·n·L customers, L = ⌈(n²/ϵ²) log(n/√δ)⌉; reason: the printed O(·) omits an additive 1: at ϵ = n the logarithm is 0 but the first pass still displays up to n rankings to L ≥ 1 customers each (counterexample to the literal reading: ϵ = n, δ < 1); the explicit count is the paper's own (p. 29 display n³/ϵ²·(1 + log1+α(n/ϵ))·log(n/√δ), and the count of p. 64), and it implies the printed O(·) when log_{1+α}(n/ϵ) ≥ 1 and the unrounded sample size is at least 1; no case is excluded
--   - reading: π∗ the optimal ranking (optimal solution to OffAR) → every full ranking π∗ (duplicate-free, length n); reason: the optimum is attained among finitely many full rankings, so a bound against every full ranking is equivalent to the bound against the optimum; same reading as the published goal
--   - reading: for i ∈ U do (no order specified) → an arbitrary scan order (a permutation of the products), universally quantified; products accepted during a pass leave U at once and later products of the pass are tried at the next rank; reason: the page leaves the order free, so the theorem must hold for every order
--   - reading: returns a ranking π̃ (which may contain fewer than n products, p. 26) → the bound is stated for the returned, possibly partial, list itself; reason: the page says the remaining products may be appended 'without affecting the theoretical bounds'; appending products cannot decrease the expected hook (resp. revenue), so the bound for the returned list implies the one after appending
--   - encoding: the fraction of customers who only click on i, under the sequential click law with bias → each customer is a pair (θ, L) with θ ∼ D and like-profile L from the coupled first-click law (independent Bernoulli(pᵢ) coordinates); the algorithm observes the indicator noClickTop(σ ∪ i, r) ∧ clicksAt(σ ∪ i, r); reason: until her first click a customer clicks each product in her window with probability pᵢ + fᵢ(∅) = pᵢ (p. 53, published first_click_identity), so this indicator has exactly the law of the paper's 'clicks on the product at rank r without clicking on any of the previously ranked products' (p. 61); p. 28 notes the algorithms only use first clicks
--   - encoding: display a ranking to L customers (fresh arrivals, types i.i.d. from D) → a stream Z s, s ∈ ℕ, of measurable, mutually independent (iIndepFun) customers on an abstract probability space, each with the stated law; the run is a deterministic function of the realized stream, customers consumed in order; reason: the learning phase consumes fresh i.i.d. customers; the sanity file proves these hypotheses satisfiable (infinite product measure)
--   - encoding: L = (n²/ϵ²) log(n/√δ) → ⌈(n²/ϵ²) log(n/√δ)⌉ (Nat.ceil, natural logarithm); reason: a number of customers is a natural number; rounding up only enlarges the sample, and the count bound uses the same rounded L
--   - encoding: τmax = 1 ≥ τmin = ϵ/n > 0 (Algorithm 3's input condition) → hypotheses 0 < ϵ, 0 < δ, 0 < α and ϵ/n ≤ 1; reason: the input condition of Algorithm 3 at the theorem's parameters
--   - encoding: types drawn from an arbitrary distribution D → a probability measure D on a measurable type space Θ and a type map τ with TypeMeasurable τ; reason: as in every published base item: without measurability the expectations ∫ … ∂D would be junk zeros; the paper's expectations presuppose it
--   - encoding: with probability (1 − δ) → ENNReal.ofReal (1 − δ) ≤ P{ω | …}; reason: 'with probability 1 − δ' is read as 'at least 1 − δ', as in the published goal; ofReal makes the bound vacuous for δ ≥ 1
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 27, Theorem 4; p. 26, Algorithm 3; p. 29 (learning-phase count); pp. 60–64, proof of Theorem 4 (premise p. 60, union bound (33) and footnote 18 p. 62)

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Threshold

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory ProbabilityTheory

/-- Theorem 4 (p. 27). Customers `Z 0, Z 1, …` arrive i.i.d., each a type `θ ∼ D` with a
like-profile from the coupled first-click law. For every scan order of the products, the Threshold
Acceptance Algorithm (Algorithm 3) with `τmax = 1`, `τmin = ϵ/n` and `L = ⌈(n²/ϵ²) log(n/√δ)⌉`:
(1) on every realization consumes at most `(1 + ⌊log_{1+α}(n/ϵ)⌋)·n·L` customers;
(2) with probability at least `1 − δ` returns a ranking `π̃` with
`E[H(π̃)] ≥ E[H(π∗)]/(2 + α) − ϵ` for every full ranking `π∗`.
The proof's premise `log_{1+α}(n/ϵ) ≤ n` (p. 60) is a hypothesis. -/
theorem theorem_4 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (eps delta α : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) (hα : 0 < α)
    (heps_le : eps / n ≤ 1)
    (hpremise : Real.logb (1 + α) (n / eps) ≤ n)
    (order : List (Fin n)) (horder : order.Perm (List.finRange n))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Θ × (Fin n → Bool)) (hZmeas : ∀ s, Measurable (Z s))
    (hZindep : iIndepFun Z P) (hZlaw : ∀ s, P.map (Z s) = customerLaw D τ) :
    (∀ ω, (thresholdAcceptance τ eps delta α order (fun s => Z s ω)).used ≤
        (1 + ⌊Real.logb (1 + α) (n / eps)⌋₊) * n * sampleSize n eps delta) ∧
      ENNReal.ofReal (1 - delta) ≤
        P {ω | ∀ piStar : List (Fin n), piStar.Nodup → piStar.length = n →
                1 / (2 + α) * expHook D τ piStar - eps ≤
                  expHook D τ (thresholdAcceptance τ eps delta α order (fun s => Z s ω)).ranked} := by sorry

end RankAssort.SimpleLearn.Supplement
