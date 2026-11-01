-- Prove2me | Theorems.Thm_PrefDeals_eq_10_private_signal_gap
-- name    : PrefDeals.eq_10_private_signal_gap
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:23.501102+00:00
-- url     : https://prove2.me/theorems/429698fe-ed6a-4685-ac4a-d722fa769fd8
-- title:
--   Eq. (10) — the common value cancels from the opportunity cost (corrected: on residual streams, not on an arbitrary impression set)
-- statement:
--   Let $S$ be a set of buyers, $A$ a stream residual for $S$, $j\in S$ with $S\setminus\{j\}\neq\emptyset$, and $\theta$ a threshold with $P(A\cap\{v_j\ge\theta\})>0$. Then
--
--   $$
--   \mathrm E_A\bigl[v_j-v_{(1)}(S\setminus\{j\})\bigm| v_j\ge\theta\bigr]=\mathrm E_A[\nu_j\mid v_j\ge\theta]-\mathrm E_A\Bigl[\max_{k\in S\setminus\{j\}}\nu_k\Bigr],
--   $$
--
--   where $\mathrm E_A[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ and $\mathrm E_A[X]=\int_A X\,dP/P(A)$.
--
--   The common component cancels in $v_j-v_{(1)}(S\setminus\{j\})$, and the other buyers' signals are independent of the conditioning event. The identity drives Lemma 4.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - correction: "for any impression set $\mathcal I$" → a stream residual for $S$: an event of $\sigma(\eta_0,\nu_k:k\notin S)$; reason: the printed statement is false for an arbitrary impression set: with $\eta_0=0$, $S=\{j,k\}$, $\nu_j,\nu_k$ uniform on $[0,1]$, $\theta_j=\tfrac12$ and $\mathcal I=\{\nu_j\ge\tfrac12,\nu_k\ge\tfrac12\}\cup\{\nu_j<\tfrac12,\nu_k<\tfrac12\}$, the left side of (10) is $\tfrac34-\tfrac34=0$ and the right side $\tfrac34-\tfrac12=\tfrac14$; residual streams are the ones on which the paper uses (10) (p.28: "the private signals $\nu_j$ for the buyers in $S$ are independent and unconditioned"), and every stream the algorithm reaches is one
--   - encoding: "for any impression set $\mathcal I$, set of buyers $S$ and buyer $j\in S$", with $\Pr_{\mathcal I}[v_j\ge\theta_j]$ cancelled → $S\setminus\{j\}\neq\emptyset$ and $P(A\cap\{v_j\ge\theta\})>0$; reason: $\max_{k\in\emptyset}\nu_k$ is undefined in the source, and the cancellation divides by $\Pr_{\mathcal I}[v_j\ge\theta_j]$
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, eq. (10), pp.25–26

import Mathlib
import Definitions.Def_PrefDeals_vmax
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **Eq. (10): the gap to the other buyers' highest valuation.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Appendix A.3.1, pp.25–26: "For any
impression set `𝓘`, set of buyers `S` and buyer `j ∈ S`, we have … Cancelling the term
`Pr_𝓘[vⱼ ≥ θⱼ]` on both sides, the last expression simplifies to the following form which we use
below: `E_𝓘[vⱼ − v₍₁₎(S \ {j})|vⱼ ≥ θⱼ] = E_𝓘[νⱼ|vⱼ ≥ θⱼ] − E_𝓘[max_{k∈S\{j}} {νₖ}]`. (10)"

Let `S` be a set of buyers, `A` a stream residual for `S` (an event of `σ(η₀, νₖ : k ∉ S)`),
`j ∈ S` with `S \ {j} ≠ ∅`, and `θ` a threshold with `P(A ∩ {vⱼ ≥ θ}) > 0`. Then

`E_A[vⱼ − v₍₁₎(S \ {j}) | vⱼ ≥ θ] = E_A[νⱼ | vⱼ ≥ θ] − E_A[max_{k ∈ S \ {j}} νₖ]`,

where `E_A[X | E] = ∫_{A∩E} X dP / P(A ∩ E)` and `E_A[X] = ∫_A X dP / P(A)`.

**Formalization Note (correction).** The printed "for any impression set `𝓘`" is corrected to the
streams the algorithm reaches with buyer set `S`, which are the residual ones (p.28). On an
arbitrary set of impressions the signals `νₖ`, `k ∈ S \ {j}`, need not be independent of the
conditioning event and (10) fails: with `η₀ = 0`, `S = {j, k}`, `νⱼ, νₖ` uniform on `[0, 1]`,
`θ = 1/2` and `𝓘 = {νⱼ ≥ 1/2, νₖ ≥ 1/2} ∪ {νⱼ < 1/2, νₖ < 1/2}`, the left side is `0` and the right
side `3/4 − 1/2 = 1/4`. -/
theorem eq_10_private_signal_gap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (S : Finset (Fin n)) (A : Set Ω) (hA : IsResidual M S A)
    (j : Fin n) (hj : j ∈ S) (hS : (S.erase j).Nonempty) (θ : ℝ)
    (hpos : 0 < P (A ∩ {ω | θ ≤ M.v j ω})) :
    (∫ ω in A ∩ {ω | θ ≤ M.v j ω}, (M.v j ω - vmax M (S.erase j) ω) ∂P) /
        P.real (A ∩ {ω | θ ≤ M.v j ω}) =
      (∫ ω in A ∩ {ω | θ ≤ M.v j ω}, M.nu j ω ∂P) / P.real (A ∩ {ω | θ ≤ M.v j ω}) -
        (∫ ω in A, (S.erase j).sup' hS (fun k => M.nu k ω) ∂P) / P.real A := by sorry

end PrefDeals
