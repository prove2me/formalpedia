-- Prove2me | Theorems.Thm_PrefDeals_aag_deal_revenue
-- name    : PrefDeals.aag_deal_revenue
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:12.187638+00:00
-- url     : https://prove2.me/theorems/f287dfe2-57b3-42ae-bfe7-d555d3acac3e
-- title:
--   Revenue of an Auction-Adjusted Greedy deal: buyer $i$ buys $\{v_i\ge\theta_i\}$ and pays $\Pr[v_i\ge\theta_i]\,\mathrm E[v_i\mid v_i\ge\theta_i]$
-- statement:
--   Let $A$ be a measurable stream and $S$ a set of buyers; deals are evaluated with the buyers' behaviour of §2, starting with the impressions of $A$ unsold.
--
--   1. If $S_1=\{i\}$, the deal $(\mathrm E_A[v_i],1,A)$ followed by any empty deals earns $\int_A v_i\,dP$.
--   2. If $|S_1|\ge2$ and $i\in S_1$ maximizes $\rho_j$ over $S_1$, then buyer $i$ accepts $(\rho_i,\mu_i,A)$ and buys $A\cap\{v_i\ge\theta_i\}$ up to a null set; and for every output $\mathit{out}'$ of the algorithm on $(A\cap\{v_i<\theta_i\},\,S_1\setminus\{i\})$ and any list of empty deals $\mathcal D_0$,
--
--   $$
--   \mathrm{Rev}_A\bigl((i,(\rho_i,\mu_i,A))\,\mathit{out}'\,\mathcal D_0\bigr)=\int_{A\cap\{v_i\ge\theta_i\}}v_i\,dP+\mathrm{Rev}_{A\cap\{v_i<\theta_i\}}(\mathit{out}') .
--   $$
--
--   Here $\mathrm{Rev}_U$ is the revenue of a sequence processed with the impressions of $U$ initially unsold. On $A=\Omega$, the first term is the paper's $\Pr[v_i\ge\theta_i]\,\mathrm E[v_i\mid v_i\ge\theta_i]$. This links the revenue of the deals the algorithm outputs to the recursion used in the proof of Theorem 2.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: the buyer "agrees to purchase a fraction $\mu_i$ of the impressions in $\mathcal I_i$" and "receives impressions that are not purchased by the buyers with higher priorities" (pp.8–9), with the single-deal behaviour of p.6 → the buyer receives $R=\mathcal I_i\cap U$ ($U$ the unsold impressions), buys $R\cap\{v_j\ge\min(\rho,q)\}$ with $q$ the top-$\mu$ quantile of $v_j$ on $R$, and accepts iff the expected utility $\int(v_j-\rho)$ of that purchase is $\ge0$ (an indifferent buyer accepts); reason: this is the p.6 behaviour applied to what reaches the buyer; for the algorithm's deals $\mathcal I_i\cap U=\mathcal I_i$, and its deals extract the full surplus (p.10), which the tie rule keeps
--   - encoding: the per-impression revenue $\Pr_{\mathcal I}[v_i\ge\theta_i]\mathrm E_{\mathcal I}[v_i\mid v_i\ge\theta_i]$ of buyer $i$ and of the recursive call → the same inequality multiplied by $P(A)$ (or by the positive conditioning mass): set integrals $\int_{A\cap E}X\,dP$ instead of $\Pr_{\mathcal I}[E]\,\mathrm E_{\mathcal I}[X\mid E]$; reason: multiplying by a positive constant changes nothing; it avoids Lean's junk value $x/0=0$
--   - generalization: the empty deals $\mathcal D_0$ of the buyers in $S_0$ → any list of empty deals; reason: empty deals sell nothing; the list $\mathcal D_0$ of the algorithm is one such list
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Appendix A.3.1, p.25 ("The algorithm obtains the expected per-impression revenue of ..."; "For any $S$ with $S_1=\{i\}$ ..."), with the buyer behaviour of §2, p.6

import Mathlib
import Definitions.Def_PrefDeals_AAGRun
import Definitions.Def_PrefDeals_dealRevenue

open MeasureTheory

namespace PrefDeals

/-- **The revenue of an Auction-Adjusted Greedy deal.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Appendix A.3.1, p.25: "For any `S`
with `S₁ = {i}`, the claim trivially follows using the deal `(ρᵢ = E[vᵢ], µᵢ = 1, 𝓘ᵢ = 𝓘)`", and
"The algorithm obtains the expected per-impression revenue of `Pr_𝓘[vᵢ ≥ θᵢ]E_𝓘[vᵢ|vᵢ ≥ θᵢ]`", with
the buyer's behaviour of §2, p.6.

Let `A` be a measurable stream and `S` a set of buyers. Deals are evaluated with the buyers'
behaviour (`boughtSet`), starting with the impressions of `A` unsold.
1. If `S₁ = {i}`, the deal `(E_A[vᵢ], 1, A)` followed by any empty deals earns `∫_A vᵢ dP`.
2. If `|S₁| ≥ 2` and `i ∈ S₁` maximizes `ρⱼ` over `S₁` (rule (2)), then buyer `i` accepts the deal
   `(ρᵢ, µᵢ, A)` and buys `A ∩ {vᵢ ≥ θᵢ}` up to a `P`-null set. For every output `out'` of the
   algorithm on `A ∩ {vᵢ < θᵢ}` with buyers `S₁ \ {i}`, the sequence `(i, (ρᵢ, µᵢ, A))`, then `out'`,
   then any empty deals, earns `∫_{A ∩ {vᵢ ≥ θᵢ}} vᵢ dP` plus what `out'` earns on `A ∩ {vᵢ < θᵢ}`.

**Formalization Note.** Revenues are unnormalized (`ρ · P(bought set)`); on `A = Ω` they are the
paper's per-impression revenues. -/
theorem aag_deal_revenue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (A : Set Ω) (hA : MeasurableSet A) (S : Finset (Fin n)) :
    (∀ i : Fin n, aagS1 M A S = {i} → ∀ l : List (Fin n),
        revenueFrom M ((i, aagSingletonDeal M A i) :: l.map fun j => (j, Deal.empty)) A =
          ∫ ω in A, M.v i ω ∂P) ∧
    (∀ i ∈ aagS1 M A S, 2 ≤ (aagS1 M A S).card →
        (∀ j ∈ aagS1 M A S, aagRho M A S j ≤ aagRho M A S i) →
        ∀ (l : List (Fin n)) (out' : List (Fin n × Deal Ω)),
          AAGRun M (A ∩ {ω | M.v i ω < aagTheta M A S i}) ((aagS1 M A S).erase i) out' →
          boughtSet M i (aagDeal M A S i) A =ᵐ[P] (A ∩ {ω | aagTheta M A S i ≤ M.v i ω} : Set Ω) ∧
          revenueFrom M ((i, aagDeal M A S i) :: (out' ++ l.map fun j => (j, Deal.empty))) A =
            (∫ ω in A ∩ {ω | aagTheta M A S i ≤ M.v i ω}, M.v i ω ∂P) +
              revenueFrom M out' (A ∩ {ω | M.v i ω < aagTheta M A S i})) := by sorry

end PrefDeals
