-- Prove2me | Theorems.Thm_PrefDeals_theorem_2
-- name    : PrefDeals.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:02.950451+00:00
-- url     : https://prove2.me/theorems/b6a3d26b-eab1-43d1-b5c4-15a1b48db798
-- title:
--   Theorem 2 — Auction-Adjusted Greedy earns $\ge\frac13$ of the optimal revenue ($\ge\frac12$ for independent valuations), at non-increasing prices
-- statement:
--   Let $n\ge1$ buyers have valuations $v_j=\eta_0+\nu_j$ as in the valuation model, and run the Auction-Adjusted Greedy algorithm on the whole stream $\Omega$ with all buyers. Then a run exists, and for every run (every choice in the $\arg\max$ of (2)), with output sequence of deals $\mathcal D$:
--
--   1. $\mathrm{Rev}(\mathcal D)\ \ge\ \tfrac13\,\mathrm E\bigl[\max_i v_i\bigr]$;
--   2. $\mathrm{Rev}(\mathcal D)\ \ge\ \tfrac13\,\mathrm{OPT}$;
--   3. if $\eta_0=0$ almost surely (independent valuations), $\mathrm{Rev}(\mathcal D)\ge\tfrac12\,\mathrm E[\max_i v_i]$ and $\mathrm{Rev}(\mathcal D)\ge\tfrac12\,\mathrm{OPT}$;
--   4. the prices per impression of the deals of $\mathcal D$ are non-increasing along the sequence.
--
--   Here $\mathrm{Rev}(\mathcal D)$ is the expected per-impression revenue of the deals $\mathcal D$ when each buyer, in priority order, receives the impressions not bought before him and responds as in §2, and $\mathrm{OPT}$ is the supremum of that revenue over all priority sequences of deals.
--
--   The algorithm is a polynomial-time, greedy way to design a sequence of preferred deals, while finding the optimal sequence is NP-hard (Theorem 1 of the paper). Non-increasing prices let the impressions be allocated at the highest price among interested buyers, as in Google's Preferred Deals.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: the buyer "agrees to purchase a fraction $\mu_i$ of the impressions in $\mathcal I_i$" and "receives impressions that are not purchased by the buyers with higher priorities" (pp.8–9), with the single-deal behaviour of p.6 → the buyer receives $R=\mathcal I_i\cap U$ ($U$ the unsold impressions), buys $R\cap\{v_j\ge\min(\rho,q)\}$ with $q$ the top-$\mu$ quantile of $v_j$ on $R$, and accepts iff the expected utility $\int(v_j-\rho)$ of that purchase is $\ge0$ (an indifferent buyer accepts); reason: this is the p.6 behaviour applied to what reaches the buyer; for the algorithm's deals $\mathcal I_i\cap U=\mathcal I_i$, and its deals extract the full surplus (p.10), which the tie rule keeps
--   - reading: "For correlated valuations (i.e., $\eta_0>0$)" → every model ($\eta_0\ge0$ almost surely), which includes $\eta_0=0$; reason: the correlated case is the general model of §4; the constant 2 also holds when $\eta_0=0$
--   - generalization: "the optimal revenue" (the paper's $\omega(\mathcal I,S)$ of (1) uses surplus-extracting deals) → the supremum over all admissible priority sequences of deals with arbitrary $(\rho,\mu,\mathcal I)$; reason: the supremum over a larger class is at least the paper's optimum, so the guarantee covers it
--   - encoding: "the sequence of deals found by Auction-Adjusted Greedy algorithm" (any $i\in\arg\max$ in (2)) → an inductive run relation; existence of a run is a conclusion, and the guarantees hold for every run; reason: covers every tie-break of (2); the paper presupposes that the smallest thresholds exist, which the existence clause asserts
--   - encoding: the prices $\rho_i$ of the deals are non-increasing over the sequence → the prices along the whole output list, the empty deals (price $0$) included, are pairwise non-increasing; reason: the empty deals come last and have price $0$, below every other price
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Theorem 2, p.12 (proof Appendix A.3, pp.25–29)

import Mathlib
import Definitions.Def_PrefDeals_AAGRun
import Definitions.Def_PrefDeals_optRevenue

open MeasureTheory

namespace PrefDeals

/-- **Theorem 2: Auction-Adjusted Greedy earns a third of the optimal revenue (a half under
independent valuations), at non-increasing prices.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Theorem 2, p.12: "The expected
per-impression revenue of the sequence of deals found by Auction-Adjusted Greedy algorithm is at
least `⅓ E_𝓘[maxᵢ{vᵢ}]`, hence, at least a third of the optimal revenue. For the independent
valuation (i.e., `η₀ = 0`), the algorithm obtains at least `½ E_𝓘[maxᵢ{vᵢ}]`, hence, at least a half of
the optimal revenue. Furthermore, the prices per impression, `ρᵢ`'s, of the deals are
non-increasing over the sequence."

For every number of buyers `n ≥ 1` and every valuation model `M` of §4 on a probability space
`(Ω, P)`, run the algorithm on the whole stream `Ω` with all buyers:
0. a run exists;
and for every run, with output `out` (a priority sequence of deals):
1. `dealRevenue M out ≥ ⅓ E[maxⱼ vⱼ]`;
2. `dealRevenue M out ≥ ⅓ optRevenue M`;
3. if `η₀ = 0` almost surely, `dealRevenue M out ≥ ½ E[maxⱼ vⱼ]` and `≥ ½ optRevenue M`;
4. the prices per impression along `out` are non-increasing.

**Formalization Note.** The revenue of `out` is computed from the buyers' behaviour of §2 on the
deals the algorithm outputs (`dealRevenue`), and `optRevenue` is the supremum of that revenue over
all admissible priority sequences of deals. The run relation covers every choice in the `arg max` of
(2). The guarantees 1–2 hold for every model (`η₀ ≥ 0`), including `η₀ = 0`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (M : ValuationModel P n) :
    (∃ out, AAGRun M Set.univ Finset.univ out) ∧
      ∀ out, AAGRun M Set.univ Finset.univ out →
        (1 / 3 : ℝ) * ∫ ω, vmax M Finset.univ ω ∂P ≤ dealRevenue M out ∧
        (1 / 3 : ℝ) * optRevenue M ≤ dealRevenue M out ∧
        ((∀ᵐ ω ∂P, M.eta0 ω = 0) →
          (1 / 2 : ℝ) * ∫ ω, vmax M Finset.univ ω ∂P ≤ dealRevenue M out ∧
          (1 / 2 : ℝ) * optRevenue M ≤ dealRevenue M out) ∧
        (out.map fun p => p.2.price).Pairwise (· ≥ ·) := by sorry

end PrefDeals
