-- Prove2me | Theorems.Thm_PrefDeals_lemma_5
-- name    : PrefDeals.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:30.608996+00:00
-- url     : https://prove2.me/theorems/c9916b6e-5a8b-4ca2-8a1b-fa747eea97c4
-- title:
--   Lemma 5 — each buyer's proposed price per impression does not increase across iterations
-- statement:
--   Let $S$ be a set of buyers, $A$ a stream residual for $S$ with $|S_1|\ge2$, and let $i\in S_1$ maximize $\rho_j$ over $S_1$. The next iteration runs on $A'=A\cap\{v_i<\theta_i\}$ with buyers $S'=S_1\setminus\{i\}$. For every $j\in S'_1$:
--
--   1. if $|S'_1|\ge2$, the next proposed price satisfies $\rho'_j=\mathrm E_{A'}[v_j\mid v_j\ge\theta'_j]\le\rho_j$;
--   2. if $S'_1=\{j\}$, the price of the deal the next iteration returns satisfies $\mathrm E_{A'}[v_j]\le\rho_j$.
--
--   Buyers of $S'_0$ get the empty deal (price $0$) and buyer $i$ gets no further price, so every proposed price weakly falls from one iteration to the next; together with the greedy choice (2) this makes the prices along the output non-increasing.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: an arbitrary stream $\mathcal I$ → a stream residual for $S$: an event of $\sigma(\eta_0,\nu_k:k\notin $S$)$; reason: these are the streams on which the paper uses the result (p.28: "the private signals $\nu_j$ for the buyers in $S$ are independent and unconditioned"); every stream the algorithm reaches is one
--   - reading: "the proposed price per impression $\rho_j$ is non-increasing across the iterations" → the price of every buyer of $S'_1$ at the next iteration is at most his price at the current one, for every residual iteration and every choice allowed by (2); reason: the paper proves exactly this comparison for "any iteration" (p.28); along a run the comparisons chain to all iterations
--   - encoding: the proposed price $\rho'_j$ at the next iteration → $\rho'_j$ when $|S'_1|\ge2$, and $\mathrm E_{A'}[v_j]$ when $S'_1=\{j\}$; reason: these are the prices Figure 1 proposes in the two cases
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Lemma 5, p.27 (proof pp.28–29)

import Mathlib
import Definitions.Def_PrefDeals_aagDeal
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **Lemma 5: each buyer's proposed price does not increase across iterations.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Lemma 5, p.27: "For each buyer `j`,
the proposed price per impression `ρⱼ` is non-increasing across the iterations of Auction-Adjusted
Greedy algorithm."

Let `S` be a set of buyers, `A` a stream residual for `S`, `|S₁| ≥ 2`, and `i ∈ S₁` maximizing `ρⱼ` over
`S₁` (rule (2)). Let `A' = A ∩ {vᵢ < θᵢ}` and `S' = S₁ \ {i}` be the next iteration, and `j ∈ S'₁`.
1. If `|S'₁| ≥ 2`, the next price `ρ'ⱼ = E_{A'}[vⱼ | vⱼ ≥ θ'ⱼ]` satisfies `ρ'ⱼ ≤ ρⱼ`.
2. If `S'₁ = {j}`, the price `E_{A'}[vⱼ]` of the deal the next iteration returns satisfies
   `E_{A'}[vⱼ] ≤ ρⱼ`.

**Formalization Note.** Buyers of `S'₀` are offered the empty deal with price `0`, and buyer `i` gets
no further price, so the cases above are all the proposed prices of the next iteration (p.28). The
statement for all iterations follows by applying it along the run. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (S : Finset (Fin n)) (A : Set Ω) (hA : IsResidual M S A)
    (hcard : 2 ≤ (aagS1 M A S).card) (i : Fin n) (hi : i ∈ aagS1 M A S)
    (hmax : ∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i)
    (j : Fin n)
    (hj : j ∈ aagS1 M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i)) :
    (2 ≤ (aagS1 M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i)).card →
        aagRho M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i) j ≤
          aagRho M A S j) ∧
      (aagS1 M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i) = {j} →
        (aagSingletonDeal M (A ∩ {ω | M.v i ω < aagTheta M A S i}) j).price ≤
          aagRho M A S j) := by sorry

end PrefDeals
