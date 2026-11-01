-- Prove2me | Theorems.Thm_PrefDeals_eq_3_cherry_picking
-- name    : PrefDeals.eq_3_cherry_picking
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:20.225513+00:00
-- url     : https://prove2.me/theorems/a597200e-9f53-4e2b-979c-680cc4dfff23
-- title:
--   Eq. (3) — cherry-picking: $\mathrm E_{\mathcal I}[v_i\mid v_{(1)}(S_1)=v_i]\le\mathrm E_{\mathcal I}[v_i\mid v_i\ge\theta_i]$
-- statement:
--   Let $A$ be a measurable stream of impressions and $S$ a set of buyers with $|S_1|\ge2$, and let $i\in S_1$. Then the threshold $\theta_i$ is attained,
--
--   $$
--   P(A\cap\{v_i\ge\theta_i\})=P(A\cap\{v_i=v_{(1)}(S_1)\}),
--   $$
--
--   and
--
--   $$
--   \int_{A\cap\{v_i=v_{(1)}(S_1)\}} v_i\,dP\ \le\ \int_{A\cap\{v_i\ge\theta_i\}} v_i\,dP .
--   $$
--
--   Dividing by the common positive mass gives the paper's (3): buyer $i$ buys as many impressions as he would win in a second-price auction, but picks the ones he values most, so his average value on them is at least his average value where he has the highest valuation.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - encoding: (3) for the buyers in $S_1$, with $\theta_i$ "the smallest $\theta_i$ such that $\Pr_{\mathcal I}[v_i\ge\theta_i]=\Pr_{\mathcal I}[v_i=v_{(1)}(S_1)]$" → for $i\in S_1$ when $|S_1|\ge2$; the attainment of the smallest threshold is stated as a first conclusion, and (3) is multiplied by the common mass; reason: Figure 1 computes thresholds only when $|S_1|\ge2$; $\theta_i$ is an infimum in Lean, so its defining property is asserted, not assumed; the common mass is positive for $i\in S_1$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, eq. (3), p.11

import Mathlib
import Definitions.Def_PrefDeals_aagTheta

open MeasureTheory

namespace PrefDeals

/-- **Eq. (3): cherry-picking.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §4, p.11: "For the buyers in `S₁`,
threshold `θⱼ` is chosen such that buyer `j` wins exactly the same number of impressions as he
would have in a second-price auction with no reserve price. … he can now cherry-pick and choose the
impressions that maximize his valuations. Therefore, we have
`E_𝓘[vᵢ|v₍₁₎(S₁) = vᵢ] ≤ E_𝓘[vᵢ|vᵢ ≥ θᵢ]`, (3)".

For every measurable stream `A`, every set of buyers `S` with `|S₁| ≥ 2` and every `i ∈ S₁`:
1. the smallest threshold `θᵢ` is attained: `P(A ∩ {vᵢ ≥ θᵢ}) = P(A ∩ {vᵢ = v₍₁₎(S₁)})`;
2. `∫_{A ∩ {vᵢ = v₍₁₎(S₁)}} vᵢ dP ≤ ∫_{A ∩ {vᵢ ≥ θᵢ}} vᵢ dP`.

**Formalization Note.** Dividing (2) by the common mass of (1), which is positive for `i ∈ S₁`,
gives (3). Thresholds are computed only when `|S₁| ≥ 2` (Figure 1). -/
theorem eq_3_cherry_picking {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (A : Set Ω) (hA : MeasurableSet A) (S : Finset (Fin n))
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S) :
    P (A ∩ {ω | aagTheta M A S i ≤ M.v i ω}) =
        P (A ∩ {ω | M.v i ω = vmax M (aagS1 M A S) ω}) ∧
      ∫ ω in A ∩ {ω | M.v i ω = vmax M (aagS1 M A S) ω}, M.v i ω ∂P ≤
        ∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, M.v i ω ∂P := by sorry

end PrefDeals
