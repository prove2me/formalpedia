-- Prove2me | Theorems.Thm_PrefDeals_induction_c_approximation
-- name    : PrefDeals.induction_c_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:33.985984+00:00
-- url     : https://prove2.me/theorems/0bbc74b8-4164-4982-8ba5-780e58447554
-- title:
--   Induction of Appendix A.3.1 — a per-level price bound $c\,\rho_i\ge\mathrm E[v_{(1)}(S_1\setminus\{i\})\mid v_i\ge\theta_i]$ gives revenue $\ge\mathrm E[v_{(1)}(S)]/(c+1)$
-- statement:
--   Let $c\ge1$, and assume that at every level the algorithm can reach — every stream $A'$ residual for a set of buyers $S'$ with $|S'_1|\ge2$, and every buyer $i\in S'_1$ maximizing $\rho_j$ over $S'_1$ —
--
--   $$
--   \mathrm E_{A'}\bigl[v_{(1)}(S'_1\setminus\{i\})\bigm| v_i\ge\theta_i\bigr]\ \le\ c\,\rho_i .
--   $$
--
--   Then for every set of buyers $S$, every stream $A$ residual for $S$ and every output $\mathit{out}$ of the algorithm on $(A,S)$,
--
--   $$
--   \int_A v_{(1)}(S)\,dP\ \le\ (c+1)\cdot\mathrm{Rev}_A(\mathit{out}),
--   $$
--
--   where $\mathrm{Rev}_A(\mathit{out})$ is the revenue of the deals $\mathit{out}$ under the buyers' behaviour of §2, processed with the impressions of $A$ initially unsold. For $A=\Omega$ this is $\mathrm E[v_{(1)}(S)]\le(c+1)\,\mathcal{AAG}(\Omega,S)$: the algorithm earns a $1/(c+1)$ fraction of the benchmark. Lemma 4 supplies the hypothesis with $c=2$ in general and $c=1$ for independent valuations.
--
--   The printed chain on p.25 drops a factor $\Pr_{\mathcal I}[v_i<\theta_i]$ in its second line; the statement here, with unnormalized integrals, does not depend on that step.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - reading: the buyer "agrees to purchase a fraction $\mu_i$ of the impressions in $\mathcal I_i$" and "receives impressions that are not purchased by the buyers with higher priorities" (pp.8–9), with the single-deal behaviour of p.6 → the buyer receives $R=\mathcal I_i\cap U$ ($U$ the unsold impressions), buys $R\cap\{v_j\ge\min(\rho,q)\}$ with $q$ the top-$\mu$ quantile of $v_j$ on $R$, and accepts iff the expected utility $\int(v_j-\rho)$ of that purchase is $\ge0$ (an indifferent buyer accepts); reason: this is the p.6 behaviour applied to what reaches the buyer; for the algorithm's deals $\mathcal I_i\cap U=\mathcal I_i$, and its deals extract the full surplus (p.10), which the tie rule keeps
--   - reading: "if $c\cdot\mathrm E_{\mathcal I}[v_i|v_i\ge\theta_i]\ge\mathrm E_{\mathcal I}[v_{(1)}(S_1\setminus\{i\})|v_i\ge\theta_i]$ for some $c\ge1$", stated at a generic level $(\mathcal I,S)$ of the induction → the bound assumed at every residual level $(A',S')$ with $|S'_1|\ge2$ and every buyer the rule (2) allows there; the conclusion for every residual $(A,S)$ and every run; reason: the induction applies the bound at every level it reaches, which are residual levels with a choice allowed by (2), and Lemma 4 proves it in exactly this form
--   - encoding: $\mathrm E_{\mathcal I}[v_{(1)}(S)]\le(c+1)\cdot\mathcal{AAG}(\mathcal I,S)$ with $\mathcal{AAG}(\mathcal I,S)$ the per-impression revenue on $\mathcal I$ → the same inequality multiplied by $P(A)$ (or by the positive conditioning mass): set integrals $\int_{A\cap E}X\,dP$ instead of $\Pr_{\mathcal I}[E]\,\mathrm E_{\mathcal I}[X\mid E]$; reason: multiplying by a positive constant changes nothing; it avoids Lean's junk value $x/0=0$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Appendix A.3.1, p.25 ("More specifically, if $c\cdot\mathrm E_{\mathcal I}[v_i|v_i\ge\theta_i]\ge\ldots$ for some $c\ge1$ ... This would yield the approximation guarantee of $\frac1{c+1}$")

import Mathlib
import Definitions.Def_PrefDeals_AAGRun
import Definitions.Def_PrefDeals_dealRevenue
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **The induction of Appendix A.3.1: a `1/(c+1)` guarantee from a per-level price bound.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Appendix A.3.1, p.25: "More
specifically, if `c · E_𝓘[vᵢ|vᵢ ≥ θᵢ] ≥ E_𝓘[v₍₁₎(S₁ \ {i})|vᵢ ≥ θᵢ]` for some `c ≥ 1` and `𝓐𝓐𝓖(𝓘, S)` is,
abusing the notation, the expected per-impression revenue of the sequence of the deals returned by
the Auction-Adjusted Greedy algorithm, we would have `E_𝓘[v₍₁₎(S)] ≤ … = (c + 1) · 𝓐𝓐𝓖(𝓘, S)` … This
would yield the approximation guarantee of `1/(c+1)`."

Let `c ≥ 1`. Assume that at every residual level `(A', S')` with `|S'₁| ≥ 2` and every buyer `i`
the algorithm may choose there (rule (2)),
`E_{A'}[v₍₁₎(S'₁ \ {i}) | vᵢ ≥ θᵢ] ≤ c · ρᵢ`. Then for every set of buyers `S`, every stream `A` residual
for `S` and every output `out` of the algorithm on `(A, S)`,

`∫_A v₍₁₎(S) dP ≤ (c + 1) · (revenue of out, processed on A)`.

**Formalization Note.** Both sides are unnormalized (multiplied by `P(A)`); with `A = Ω` this is
`E[v₍₁₎(S)] ≤ (c+1) · 𝓐𝓐𝓖(Ω, S)`. The revenue is that of the output deals under the buyers'
behaviour of §2 (`revenueFrom`), not a recursion. The induction of p.25 applies the price bound at
every level it reaches; those are residual levels with a choice allowed by (2). The printed chain
drops a factor `Pr_𝓘[vᵢ < θᵢ]` in its second line; the unnormalized form has no such factor. -/
theorem induction_c_approximation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n) (c : ℝ) (hc : 1 ≤ c)
    (hlevel : ∀ (A' : Set Ω) (S' : Finset (Fin n)), IsResidual M S' A' →
      2 ≤ (aagS1 M A' S').card → ∀ i ∈ aagS1 M A' S',
      (∀ j ∈ aagS1 M A' S', aagRho M A' S' j ≤ aagRho M A' S' i) →
      (∫ ω in A' ∩ {ω | aagTheta M A' S' i ≤ M.v i ω}, vmax M ((aagS1 M A' S').erase i) ω ∂P) /
          P.real (A' ∩ {ω | aagTheta M A' S' i ≤ M.v i ω}) ≤ c * aagRho M A' S' i)
    (S : Finset (Fin n)) (A : Set Ω) (hA : IsResidual M S A)
    (out : List (Fin n × Deal Ω)) (hrun : AAGRun M A S out) :
    ∫ ω in A, vmax M S ω ∂P ≤ (c + 1) * revenueFrom M out A := by sorry

end PrefDeals
