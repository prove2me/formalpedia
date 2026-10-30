-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_lemma_2_revenue_le_sum_price_prob
-- name    : SeqPostedPricing.MatroidSPM.lemma_2_revenue_le_sum_price_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:53.362131+00:00
-- url     : https://prove2.me/theorems/82cd2ea8-c719-4bd6-8718-9bbe32749da4
-- title:
--   Lemma 2: for regular values, $\mathcal R^M\le\sum_i p_i^Mq_i^M$ (corrected: individually rational mechanisms)
-- statement:
--   Let the values $v_1,\dots,v_n$ be independent, $v_i\sim\mu_i$ with $\mu_i$ regular, let $\mathcal J$ be any feasibility constraint, and let $M$ be an admissible mechanism (feasible, truthful, individually rational, with measurable allocation events and integrable payments). Let $q_i^M$ be the probability that $M$ serves agent $i$, and for every agent with $q_i^M>0$ let $p_i^M=F_i^{-1}(1-q_i^M)$. Then
--
--   $$
--   \mathcal R^M\le\sum_{i=1}^n p_i^M\,q_i^M .
--   $$
--
--   The bound replaces the revenue of the optimal mechanism by the revenue of $n$ independent single-agent take-it-or-leave-it offers that sell with the same probabilities; it is the benchmark the sequential posted-price mechanism is compared with.
--
--   Differences from the source:
--   - correction: for any truthful mechanism M → for any admissible M: truthful and individually rational (plus feasibility, measurable allocation events, integrable payments); reason: a truthful mechanism that never serves and charges agent 1 a fee of 1 has revenue 1 > Σ_i p_i q_i = 0; the paper's mechanisms are individually rational (Lemma 3, App. A: unserved agents pay nothing)
--   - encoding: revenue and q_i^M as expectations → measurable allocation events and integrable payments in `IsAdmissible`; reason: Lean's integral is 0 on non-integrable functions; these clauses only make R^M and q_i^M defined
--   - reading: regular: φ(v) = v − (1 − F(v))/f(v) monotone non-decreasing → a density f with f > 0 wherever 0 < F < 1 and φ monotone on {0 < F < 1} (`IsRegular`); reason: φ is undefined where f = 0 and is read as −∞ there, so monotonicity rules out a density gap inside the support; under the other reading Lemma 2 fails (v ∼ ½U[0,1] + ½U[10,11], a mechanism posting 10 w.p. 0.9 and 0 w.p. 0.1 earns 4.5 > p q = 0.495)
--   - reading: p_i = F_i^{−1}(1 − q_i) → the largest p with Pr[v_i > p] = q_i (`IsQuantilePrice`), required only for agents with q_i > 0; reason: the inverse is unique for 0 < q_i < 1 under regularity and at q_i = 1 is the bottom of the support; agents with q_i = 0 contribute nothing
--   - generalization: M a mechanism over the n agents (implicitly for the instance's constraint J) → any feasibility predicate `Feas` with M's allocations feasible; reason: the bound does not use feasibility; `Feas = fun _ => True` is the unconstrained case, so the source's claim is a special case
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2 (first sentence), p. 5; proof in App. A, p. 13

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsAdmissible
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice
import Definitions.Def_SeqPostedPricing_MatroidSPM_revenue
import Definitions.Def_SeqPostedPricing_MatroidSPM_allocProb
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmActive
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Lemma 2 (first sentence): for regular distributions, the revenue of a truthful mechanism is
at most `Σ_i p_i^M q_i^M`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, Lemma 2, p. 5 (PDF p. 7); proof in App. A, p. 13 (PDF p. 15): "If Fi is regular for each i,
for any truthful mechanism M over the n agents, the revenue of M is bounded from above by
Σ_i p_i^M q_i^M where q_i^M is the probability (over v1, · · · , vn) with which M allocates to
agent i and p_i^M = Fi^{−1}(1 − q_i^M)."

For independent regular values `v_i ∼ μ i`, every admissible mechanism `M` (for any feasibility
constraint) and every choice of prices `p_i = F_i^{−1}(1 − q_i^M)` for the agents with
`q_i^M > 0`: `R^M ≤ Σ_i p_i q_i^M`.

**Formalization Note.** "Truthful mechanism" is read as an admissible mechanism: truthful and
individually rational (the paper's mechanisms are; without individual rationality a mechanism
could charge every agent a fixed fee and the bound fails), with measurable allocation events and
integrable payments so that `q_i^M` and `R^M` are meaningful. The feasibility constraint `Feas`
is arbitrary (`Feas = fun _ => True` gives no constraint). Agents with `q_i^M = 0` contribute `0`
to the sum whatever their price, so their price is not constrained. `F_i^{−1}(1 − q)` is the
largest price with tail probability `q` (`IsQuantilePrice`). -/
theorem lemma_2_revenue_le_sum_price_prob {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (hreg : ∀ i, IsRegular (μ i))
    (M : Mechanism n) (hM : IsAdmissible Feas μ M)
    (p : Fin n → ℝ) (hp : ∀ i ∈ spmActive μ M, IsQuantilePrice (μ i) (allocProb μ M i) (p i)) :
    revenue μ M ≤ ∑ i, p i * allocProb μ M i := by sorry

end SeqPostedPricing.MatroidSPM
