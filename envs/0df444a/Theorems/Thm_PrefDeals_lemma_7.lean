-- Prove2me | Theorems.Thm_PrefDeals_lemma_7
-- name    : PrefDeals.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:27.583674+00:00
-- url     : https://prove2.me/theorems/d5e3b4b9-46c8-4951-935b-917047eed0cb
-- title:
--   Lemma 7 — $\Pr_{\mathcal I}[v_j\ge\theta_j\mid v_i<\theta_i]\le\Pr_{\mathcal I}[v_j\ge\theta_j]$ (corrected: on residual streams, not on an arbitrary impression set)
-- statement:
--   Let $i,j$ be buyers, $\theta_i,\theta_j$ any thresholds, and $A$ a stream residual for $\{i,j\}$, i.e. an event of $\sigma(\eta_0,\nu_k:k\notin\{i,j\})$, with $P(A\cap\{v_i<\theta_i\})>0$. Then
--
--   $$
--   \Pr_A[v_j\ge\theta_j\mid v_i<\theta_i]=\frac{P(A\cap\{v_i<\theta_i\}\cap\{v_j\ge\theta_j\})}{P(A\cap\{v_i<\theta_i\})}\ \le\ \frac{P(A\cap\{v_j\ge\theta_j\})}{P(A)}=\Pr_A[v_j\ge\theta_j].
--   $$
--
--   Learning that buyer $i$'s valuation is low makes a high common value less likely, and hence buyer $j$'s valuation stochastically smaller. The paper uses it to show that thresholds and prices only fall along the algorithm (Claim 1, Lemma 5).
--
--   As printed, for an arbitrary set of impressions, the statement is false: with $\eta_0=0$, $\nu_i,\nu_j$ uniform on $[0,1]$, $\theta_i=\theta_j=1/2$ and $\mathcal I=\{\nu_i<1/2,\nu_j\ge1/2\}\cup\{\nu_i\ge1/2\}$, the left side is $1$ and the right side $2/3$.
--
--   Differences from the source:
--   - encoding: a stream of impressions $\mathcal I$ drawn i.i.d., with per-impression quantities $\Pr_{\mathcal I}$, $\mathrm E_{\mathcal I}$ → a probability space $(\Omega,P)$ whose points are impressions; $\Pr_{\mathcal I}[E]=P(A\cap E)/P(A)$ and $\mathrm E_{\mathcal I}[X\mid E]=\int_{A\cap E}X\,dP/P(A\cap E)$ for a measurable stream $A$; reason: the paper's quantities are expectations over the impression distribution (the purchase requirement is met in expectation, p.6); same values
--   - encoding: nonnegative $\eta_0$ and $\nu_j$ obtained by shifting "without loss of generality" (p.10) → $0\le\underline\eta$ and $0\le\underline\nu_j$ as hypotheses of the model; reason: the paper's own normalization; shifting leaves every valuation and the algorithm unchanged
--   - generalization: $\eta_0$ distributed over $[\underline\eta,\bar\eta]$ with a density $f^{\eta_0}$ (p.27), so that the margins of $v_i$ are bounded and positive on $[\underline v_i,\bar v_i]$ (p.10) → any law of $\eta_0$ on $[\underline\eta,\bar\eta]\subset[0,\infty)$; the signals $\nu_j$ are only required to have densities (the paper's $f^{\nu_j}$, p.25) vanishing outside $[\underline\nu_j,\bar\nu_j]$, not bounded or positive densities; reason: every model of the paper is a model here (including $\eta_0=0$); the arguments use $\eta_0$ only through independence, boundedness and nonnegativity, and the signals only through their densities (no atoms, so ties are null) and supports
--   - correction: "Assume $\mathcal I$ is an arbitrary set of impressions" → a stream residual for $\{i,j\}$: an event of $\sigma(\eta_0,\nu_k:k\notin\{i,j\})$; reason: the printed statement is false for an arbitrary impression set: with $\eta_0=0$, $\nu_i,\nu_j$ uniform on $[0,1]$, $\theta_i=\theta_j=\tfrac12$ and $\mathcal I=\{\nu_i<\tfrac12,\nu_j\ge\tfrac12\}\cup\{\nu_i\ge\tfrac12\}$, $\Pr_{\mathcal I}[v_j\ge\tfrac12\mid v_i<\tfrac12]=1>\tfrac23=\Pr_{\mathcal I}[v_j\ge\tfrac12]$; residual streams are the ones on which the paper uses the lemma (p.28: "the private signals $\nu_j$ for the buyers in $S$ are independent and unconditioned"), and every stream the algorithm reaches is one
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Lemma 7, p.27

import Mathlib
import Definitions.Def_PrefDeals_IsResidual

open MeasureTheory

namespace PrefDeals

/-- **Lemma 7: a low valuation of one buyer makes another's high valuation less likely.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Lemma 7, p.27: "Assume `𝓘` is an
arbitrary set of impressions and buyers `i` and `j` have arbitrary thresholds `θᵢ` and `θⱼ` such that
`Pr_𝓘[vᵢ < θᵢ] > 0`. Then, `Pr_𝓘[vⱼ ≥ θⱼ|vᵢ < θᵢ] ≤ Pr_𝓘[vⱼ ≥ θⱼ]`."

Let `i, j` be buyers, `θᵢ, θⱼ` any thresholds, and `A` a stream residual for `{i, j}` (an event of
`σ(η₀, νₖ : k ∉ {i, j})`) with `P(A ∩ {vᵢ < θᵢ}) > 0`. Then

`P(A ∩ {vᵢ < θᵢ} ∩ {vⱼ ≥ θⱼ}) / P(A ∩ {vᵢ < θᵢ}) ≤ P(A ∩ {vⱼ ≥ θⱼ}) / P(A)`.

**Formalization Note (correction).** The printed "arbitrary set of impressions" is corrected to a
stream the algorithm can reach while `i` and `j` are still unserved, as in the paper's use of the
lemma (p.28). For an arbitrary measurable set the printed statement is false: with `η₀ = 0`, `νᵢ, νⱼ` uniform on `[0, 1]`,
`θᵢ = θⱼ = 1/2` and `𝓘 = {νᵢ < 1/2, νⱼ ≥ 1/2} ∪ {νᵢ ≥ 1/2}`, the left side is `1` and the right side
`2/3`. The buyers `i` and `j` may coincide (then `A` is residual for `{i}`). -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (M : ValuationModel P n)
    (i j : Fin n) (θi θj : ℝ) (A : Set Ω) (hA : IsResidual M {i, j} A)
    (hpos : 0 < P (A ∩ {ω | M.v i ω < θi})) :
    P.real (A ∩ {ω | M.v i ω < θi} ∩ {ω | θj ≤ M.v j ω}) / P.real (A ∩ {ω | M.v i ω < θi}) ≤
      P.real (A ∩ {ω | θj ≤ M.v j ω}) / P.real A := by sorry

end PrefDeals
