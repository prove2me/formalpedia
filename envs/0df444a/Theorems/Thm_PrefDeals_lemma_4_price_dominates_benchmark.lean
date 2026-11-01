-- Prove2me | Theorems.Thm_PrefDeals_lemma_4_price_dominates_benchmark
-- name    : PrefDeals.lemma_4_price_dominates_benchmark
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:13.797492+00:00
-- url     : https://prove2.me/theorems/739683ee-49fa-478f-b02e-1b8c52b8f857
-- title:
--   Proof of Lemma 4 — $\mathrm E_{\mathcal I}[v_{(1)}(S_1)]\le\sum_{j\in S_1}\rho_j\mu_j\le\rho_i$
-- statement:
--   Let $A$ be a measurable stream and $S$ a set of buyers with $|S_1|\ge2$, and let $i\in S_1$ maximize $\rho_j$ over $S_1$. Then
--
--   $$
--   \mathrm E_A\bigl[v_{(1)}(S_1)\bigr]\ \le\ \sum_{j\in S_1}\rho_j\mu_j\ \le\ \rho_i,
--   $$
--
--   where $\mathrm E_A[X]=\int_A X\,dP/P(A)$.
--
--   The first inequality decomposes the benchmark by the winning buyer and applies (3) to each; the second holds because $\sum_{j\in S_1}\mu_j=1$ (ties are null events), so the middle term is a convex combination of the prices, and $i$ has the largest price.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Proof of Lemma 4, p.26 (display before "where we used Eq. (3)" and "Since the last expression is a convex combination ...")

import Mathlib
import Definitions.Def_PrefDeals_aagDeal

open MeasureTheory

namespace PrefDeals

/-- **Proof of Lemma 4: the chosen price dominates the stream's benchmark.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Proof of Lemma 4, p.26:
"`E_𝓘[v₍₁₎(S₁)] = Σ_{j∈S₁} E_𝓘[vⱼ 1(v₍₁₎(S₁) = vⱼ)] = … ≤ Σ_{j∈S₁} E_𝓘[vⱼ|vⱼ ≥ θⱼ] Pr_𝓘[vⱼ ≥ θⱼ]
= Σ_{j∈S₁} ρⱼ µⱼ`, … Since the last expression is a convex combination of the prices per impression
and we greedily choose buyer `i` with the maximum price per impression, we have
`E_𝓘[v₍₁₎(S₁)] ≤ ρᵢ`."

For every measurable stream `A`, every set of buyers `S` with `|S₁| ≥ 2` and every `i ∈ S₁` maximizing
`ρⱼ` over `S₁`:

`E_A[v₍₁₎(S₁)] ≤ Σ_{j ∈ S₁} ρⱼ µⱼ ≤ ρᵢ`,

where `E_A[X] = ∫_A X dP / P(A)`. -/
theorem lemma_4_price_dominates_benchmark {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (A : Set Ω) (hA : MeasurableSet A) (S : Finset (Fin n))
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S)
    (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i) :
    (∫ ω in A, vmax M (aagS1 M A S) ω ∂P) / P.real A ≤
        ∑ j ∈ aagS1 M A S, aagRho M A S j * aagMu M A S j ∧
      ∑ j ∈ aagS1 M A S, aagRho M A S j * aagMu M A S j ≤ aagRho M A S i := by sorry

end PrefDeals
