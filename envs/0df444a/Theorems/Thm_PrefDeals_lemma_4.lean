-- Prove2me | Theorems.Thm_PrefDeals_lemma_4
-- name    : PrefDeals.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:17.46199+00:00
-- url     : https://prove2.me/theorems/976467d6-991c-49fb-850f-c64ecc98211b
-- title:
--   Lemma 4 — $\mathrm E_{\mathcal I}[v_{(1)}(S_1\setminus\{i\})\mid v_i\ge\theta_i]\le2\rho_i$, and $\le\rho_i$ for independent valuations
-- statement:
--   Let $S$ be a set of buyers, $A$ a stream residual for $S$ with $|S_1|\ge2$, and let $i\in S_1$ maximize $\rho_j$ over $S_1$ (rule (2)). Write $\mathrm E_A[X\mid v_i\ge\theta_i]=\int_{A\cap\{v_i\ge\theta_i\}}X\,dP/P(A\cap\{v_i\ge\theta_i\})$, so that $\rho_i=\mathrm E_A[v_i\mid v_i\ge\theta_i]$.
--
--   1. In every model,
--   $$
--   \mathrm E_A\bigl[v_{(1)}(S_1\setminus\{i\})\bigm| v_i\ge\theta_i\bigr]\ \le\ 2\rho_i .
--   $$
--   2. If $\eta_0=0$ almost surely (independent valuations),
--   $$
--   \mathrm E_A\bigl[v_{(1)}(S_1\setminus\{i\})\bigm| v_i\ge\theta_i\bigr]\ \le\ \rho_i .
--   $$
--
--   The left side is the opportunity cost of giving buyer $i$ the impressions where $v_i\ge\theta_i$; the lemma bounds it by a constant multiple of the price $i$ pays, which yields the factors $1/3$ and $1/2$ of Theorem 2.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: an arbitrary stream $\mathcal I$ → a stream residual for $S$: an event of $\sigma(\eta_0,\nu_k:k\notin $S$)$; reason: these are the streams on which the paper uses the result (p.28: "the private signals $\nu_j$ for the buyers in $S$ are independent and unconditioned"); every stream the algorithm reaches is one
--   - reading: "For correlated valuations (i.e., $\eta_0>0$)" → every model ($\eta_0\ge0$ almost surely), which includes $\eta_0=0$; reason: the correlated case is the general model of §4; the constant 2 also holds when $\eta_0=0$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Lemma 4, p.26

import Mathlib
import Definitions.Def_PrefDeals_aagDeal
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **Lemma 4: the opportunity cost is at most twice the price (at most the price if independent).**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Lemma 4, p.26: "For correlated
valuations (i.e., `η₀ > 0`), we have `2 E_𝓘[vᵢ|vᵢ ≥ θᵢ] ≥ E_𝓘[v₍₁₎(S₁ \ {i})|vᵢ ≥ θᵢ]`. For independent
valuations (i.e., `η₀ = 0`), we have `E_𝓘[vᵢ|vᵢ ≥ θᵢ] ≥ E_𝓘[v₍₁₎(S₁ \ {i})|vᵢ ≥ θᵢ]`."

Let `S` be a set of buyers, `A` a stream residual for `S`, `|S₁| ≥ 2`, and `i ∈ S₁` maximizing `ρⱼ` over
`S₁` (rule (2)). Write `E_A[X | vᵢ ≥ θᵢ] = ∫_{A∩{vᵢ≥θᵢ}} X dP / P(A ∩ {vᵢ ≥ θᵢ})`; `ρᵢ = E_A[vᵢ | vᵢ ≥ θᵢ]`.
1. `E_A[v₍₁₎(S₁ \ {i}) | vᵢ ≥ θᵢ] ≤ 2 ρᵢ`.
2. If `η₀ = 0` almost surely, `E_A[v₍₁₎(S₁ \ {i}) | vᵢ ≥ θᵢ] ≤ ρᵢ`.

**Formalization Note.** Part 1 is stated for every model (`η₀ ≥ 0`), which includes `η₀ = 0`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (S : Finset (Fin n)) (A : Set Ω) (hA : IsResidual M S A)
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S)
    (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i) :
    (∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, vmax M ((aagS1 M A S).erase i) ω ∂P) /
          P.real (A ∩ {ω | aagTheta M A S i ≤ M.v i ω}) ≤ 2 * aagRho M A S i ∧
      ((∀ᵐ ω ∂P, M.eta0 ω = 0) →
        (∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, vmax M ((aagS1 M A S).erase i) ω ∂P) /
          P.real (A ∩ {ω | aagTheta M A S i ≤ M.v i ω}) ≤ aagRho M A S i) := by sorry

end PrefDeals
