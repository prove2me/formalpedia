-- Prove2me | Theorems.Thm_PrefDeals_eq_9_benchmark_decomposition
-- name    : PrefDeals.eq_9_benchmark_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:25.043308+00:00
-- url     : https://prove2.me/theorems/877f1158-1019-4427-850f-b8cbed87013b
-- title:
--   Eq. (9) — upper bound on the benchmark $\mathrm E_{\mathcal I}[v_{(1)}(S)]$
-- statement:
--   Let $A$ be a measurable stream and $S$ a set of buyers with $|S_1|\ge2$, and let $i\in S_1$ maximize $\rho_j$ over $S_1$. Then $\int_A v_{(1)}(S)\,dP=\int_A v_{(1)}(S_1)\,dP$ and
--
--   $$
--   \int_A v_{(1)}(S)\,dP\ \le\ \int_{A\cap\{v_i\ge\theta_i\}}v_i\,dP+\int_{A\cap\{v_i\ge\theta_i\}}v_{(1)}(S_1\setminus\{i\})\,dP+\int_{A\cap\{v_i<\theta_i\}}v_{(1)}(S_1\setminus\{i\})\,dP .
--   $$
--
--   Divided by $P(A)$ this is the paper's (9): the benchmark is at most what buyer $i$'s deal earns plus the highest value of the remaining buyers, on the impressions $i$ buys and on those he does not.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - encoding: $\mathrm E_{\mathcal I}[v_{(1)}(S)]\le\Pr_{\mathcal I}[v_i\ge\theta_i](\ldots)+\Pr_{\mathcal I}[v_i<\theta_i]\ldots$, the first and last lines of (9) → the same inequality multiplied by $P(A)$ (or by the positive conditioning mass): set integrals $\int_{A\cap E}X\,dP$ instead of $\Pr_{\mathcal I}[E]\,\mathrm E_{\mathcal I}[X\mid E]$; reason: multiplying by a positive constant changes nothing; it avoids Lean's junk value $x/0=0$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, eq. (9), p.25

import Mathlib
import Definitions.Def_PrefDeals_aagDeal

open MeasureTheory

namespace PrefDeals

/-- **Eq. (9): an upper bound on the benchmark.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Appendix A.3.1, p.25:
"`E_𝓘[v₍₁₎(S)] = E_𝓘[v₍₁₎(S₁)] = … ≤ Pr_𝓘[vᵢ ≥ θᵢ](E_𝓘[vᵢ|vᵢ ≥ θᵢ] + E_𝓘[v₍₁₎(S₁ \ {i})|vᵢ ≥ θᵢ]) +
Pr_𝓘[vᵢ < θᵢ] E_𝓘[v₍₁₎(S₁ \ {i})|vᵢ < θᵢ]`, (9)", where `i` is the buyer chosen by (2).

For every measurable stream `A`, every set of buyers `S` with `|S₁| ≥ 2` and every `i ∈ S₁` maximizing
`ρⱼ` over `S₁`:
1. `∫_A v₍₁₎(S) dP = ∫_A v₍₁₎(S₁) dP`;
2. `∫_A v₍₁₎(S) dP ≤ ∫_{A∩{vᵢ ≥ θᵢ}} vᵢ dP + ∫_{A∩{vᵢ ≥ θᵢ}} v₍₁₎(S₁ \ {i}) dP + ∫_{A∩{vᵢ < θᵢ}} v₍₁₎(S₁ \ {i}) dP`.

**Formalization Note.** Both sides of (9) are multiplied by `P(A)`: `Pr_𝓘[E] E_𝓘[X|E] = ∫_{A∩E} X dP / P(A)`. -/
theorem eq_9_benchmark_decomposition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (A : Set Ω) (hA : MeasurableSet A) (S : Finset (Fin n))
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S)
    (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i) :
    ∫ ω in A, vmax M S ω ∂P = ∫ ω in A, vmax M (aagS1 M A S) ω ∂P ∧
      ∫ ω in A, vmax M S ω ∂P ≤
        (∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, M.v i ω ∂P) +
          (∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, vmax M ((aagS1 M A S).erase i) ω ∂P) +
          ∫ ω in A ∩ {ω | M.v i ω < aagTheta M A S i}, vmax M ((aagS1 M A S).erase i) ω ∂P := by sorry

end PrefDeals
