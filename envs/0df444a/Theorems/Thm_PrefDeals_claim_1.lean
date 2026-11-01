-- Prove2me | Theorems.Thm_PrefDeals_claim_1
-- name    : PrefDeals.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:10.428045+00:00
-- url     : https://prove2.me/theorems/2494ce14-fb3f-413d-84d8-585d3a90e125
-- title:
--   Claim 1 — the thresholds do not increase from one iteration to the next: $\theta'_j\le\theta_j$
-- statement:
--   Let $S$ be a set of buyers, $A$ a stream residual for $S$ with $|S_1|\ge2$, and let $i\in S_1$ maximize $\rho_j$ over $S_1$. The next iteration of the algorithm runs on $A'=A\cap\{v_i<\theta_i\}$ with buyers $S'=S_1\setminus\{i\}$; primes denote its quantities. If it computes thresholds ($|S'_1|\ge2$), then for every $j\in S'_1$,
--
--   $$
--   \theta'_j\ \le\ \theta_j .
--   $$
--
--   With fewer competitors and on impressions where buyer $i$ values little, buyer $j$ wins at least as often, so his threshold for the same winning frequency does not rise.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: an arbitrary stream $\mathcal I$ → a stream residual for $S$: an event of $\sigma(\eta_0,\nu_k:k\notin $S$)$; reason: these are the streams on which the paper uses the result (p.28: "the private signals $\nu_j$ for the buyers in $S$ are independent and unconditioned"); every stream the algorithm reaches is one
--   - encoding: $\theta'_j$ for $j\in S'=S_1\setminus\{i\}$ → for $j\in S'_1$ when $|S'_1|\ge2$; reason: Figure 1 defines $\theta'_j$ only for $j\in S'_1$ and only when $|S'_1|\ge2$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Claim 1, p.28 (proof of Lemma 5)

import Mathlib
import Definitions.Def_PrefDeals_aagDeal
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **Claim 1: thresholds do not increase from one iteration to the next.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Proof of Lemma 5, p.28: "We use the
prime to indicate the corresponding sets and parameters in the next iteration: `𝓘'`, `S'`, `S'₀`,
`S'₁`, `{θ'ⱼ}`, … Since buyer `i` is chosen in the current iterations, we have `𝓘' = 𝓘 \ {vᵢ ≥ θᵢ}` and
`S' = S₁ \ {i}`. … Claim 1 `θ'ⱼ ≤ θⱼ`."

Let `S` be a set of buyers, `A` a stream residual for `S`, `|S₁| ≥ 2`, and `i ∈ S₁` maximizing `ρⱼ` over
`S₁` (rule (2)). Let `A' = A ∩ {vᵢ < θᵢ}` and `S' = S₁ \ {i}` be the next iteration. If the next
iteration computes thresholds (`|S'₁| ≥ 2`), then for every `j ∈ S'₁`, `θ'ⱼ ≤ θⱼ`. -/
theorem claim_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (S : Finset (Fin n)) (A : Set Ω) (hA : IsResidual M S A)
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S)
    (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i)
    (hcard' : 2 ≤ (aagS1 M (A ∩ {ω | M.v i ω < aagTheta M A S i})
      ((aagS1 M A S).erase i)).card)
    (j : Fin n)
    (hj : j ∈ aagS1 M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i)) :
    aagTheta M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i) j ≤
      aagTheta M A S j := by sorry

end PrefDeals
