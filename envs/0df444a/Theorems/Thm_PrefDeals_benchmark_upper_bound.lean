-- Prove2me | Theorems.Thm_PrefDeals_benchmark_upper_bound
-- name    : PrefDeals.benchmark_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:45.939978+00:00
-- url     : https://prove2.me/theorems/c1abe729-8f6a-4210-bc1a-d27a47052cf5
-- title:
--   The benchmark $\mathrm E[\max_i v_i]$ bounds the revenue of every sequence of deals
-- statement:
--   For every admissible priority sequence of preferred deals, with buyers behaving as in §2,
--
--   $$
--   \mathrm{Rev}(\mathit{seq})\ \le\ \mathrm E\Bigl[\max_i v_i\Bigr].
--   $$
--
--   Consequently the set of such revenues is bounded above and the optimal revenue satisfies $\mathrm{OPT}\le\mathrm E[\max_i v_i]$.
--
--   A buyer who accepts a deal pays at most his value on the impressions he buys, and different buyers buy disjoint sets of impressions. This is the benchmark the paper uses to compare the algorithm with the optimal revenue.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: the buyer "agrees to purchase a fraction $\mu_i$ of the impressions in $\mathcal I_i$" and "receives impressions that are not purchased by the buyers with higher priorities" (pp.8–9), with the single-deal behaviour of p.6 → the buyer receives $R=\mathcal I_i\cap U$ ($U$ the unsold impressions), buys $R\cap\{v_j\ge\min(\rho,q)\}$ with $q$ the top-$\mu$ quantile of $v_j$ on $R$, and accepts iff the expected utility $\int(v_j-\rho)$ of that purchase is $\ge0$ (an indifferent buyer accepts); reason: this is the p.6 behaviour applied to what reaches the buyer; for the algorithm's deals $\mathcal I_i\cap U=\mathcal I_i$, and its deals extract the full surplus (p.10), which the tie rule keeps
--   - generalization: the optimal revenue over sequences of deals (the paper's $\omega(\mathcal I,S)$ of (1) uses surplus-extracting deals) → the supremum over all admissible priority sequences of deals with arbitrary $(\rho,\mu,\mathcal I)$, lists that omit buyers included; reason: a larger class has a larger supremum, so the bound covers the paper's optimum; omitted buyers earn what an empty deal earns
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §4, p.12 ("We use $\mathrm E_{\mathcal I}[\max_i\{v_i\}]$ as the benchmark which is the trivial upper bound on the optimal revenue")

import Mathlib
import Definitions.Def_PrefDeals_optRevenue
import Definitions.Def_PrefDeals_vmax

open MeasureTheory

namespace PrefDeals

/-- **The benchmark `E_𝓘[maxᵢ{vᵢ}]` bounds the optimal revenue.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §4, p.12: "We use `E_𝓘[maxᵢ{vᵢ}]` as
the benchmark which is the trivial upper bound on the optimal revenue."

Under the buyers' behaviour of §2:
1. every admissible priority sequence of deals earns at most `E[maxⱼ vⱼ]`;
2. the set of revenues of admissible priority sequences is bounded above;
3. the optimal revenue `optRevenue M` is at most `E[maxⱼ vⱼ]`. -/
theorem benchmark_upper_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n) :
    (∀ seq : List (Fin n × Deal Ω), IsPrioritySequence seq →
        dealRevenue M seq ≤ ∫ ω, vmax M Finset.univ ω ∂P) ∧
      BddAbove (dealRevenue M '' {seq | IsPrioritySequence seq}) ∧
      optRevenue M ≤ ∫ ω, vmax M Finset.univ ω ∂P := by sorry

end PrefDeals
