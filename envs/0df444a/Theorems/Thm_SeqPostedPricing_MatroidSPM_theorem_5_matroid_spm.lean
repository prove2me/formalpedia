-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_theorem_5_matroid_spm
-- name    : SeqPostedPricing.MatroidSPM.theorem_5_matroid_spm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:14.112003+00:00
-- url     : https://prove2.me/theorems/b170c8e2-d6ed-4f02-abf0-6a147bf911d9
-- title:
--   Theorem 5: under a matroid constraint, the SPM $\mathcal S$ 2-approximates the revenue of Myerson's mechanism
-- statement:
--   Let $\mathcal J\subseteq2^{[n]}$ be a matroid, let the values $v_1,\dots,v_n$ be independent with regular distributions $v_i\sim\mu_i$, and let $M$ be a revenue-optimal mechanism (for instance Myerson's mechanism) with allocation probabilities $q_i=q_i^M$. Let $\mathcal S$ be the sequential posted-price mechanism that
--
--   1. offers service to the agents with $q_i>0$,
--   2. at prices $p_i=F_i^{-1}(1-q_i)$,
--   3. in decreasing order of price (ties broken arbitrarily), serving an agent who accepts whenever the served set stays in $\mathcal J$.
--
--   Then
--
--   $$
--   \mathcal R^M\ \le\ 2\,\mathcal R^{\mathcal S}.
--   $$
--
--   A simple, non-adaptive pricing scheme thus loses at most half of the optimal revenue under every matroid constraint, with no assumption beyond independence and regularity.
--
--   Differences from the source:
--   - generalization: Myerson's mechanism → any optimal admissible mechanism M (`IsOptimal`), with S built from M's q_i; reason: Myerson's mechanism is admissible and optimal (Theorem 19), so the paper's statement is a special case
--   - reading: regular: φ(v) = v − (1 − F(v))/f(v) monotone non-decreasing → a density f with f > 0 wherever 0 < F < 1 and φ monotone on {0 < F < 1} (`IsRegular`); reason: φ is undefined where f = 0 and is read as −∞ there, so monotonicity rules out a density gap inside the support; under the other reading Lemma 2 fails (v ∼ ½U[0,1] + ½U[10,11], a mechanism posting 10 w.p. 0.9 and 0 w.p. 0.1 earns 4.5 > p q = 0.495)
--   - reading: p_i = F_i^{−1}(1 − q_i) → the largest p with Pr[v_i > p] = q_i (`IsQuantilePrice`), required only for agents with q_i > 0; reason: the inverse is unique for 0 < q_i < 1 under regularity and at q_i = 1 is the bottom of the support; agents with q_i = 0 contribute nothing
--   - encoding: agents with q_i = 0 are offered a price they accept with probability exactly 0 → agents with q_i = 0 are not offered; reason: the outcome differs only on a null event
--   - encoding: agent accepts a price → p_i ≤ v_i; reason: §1: accept iff the price is no more than the value
--   - generalization: "in decreasing order of their prices" → every order non-increasing in price on the offered agents (any tie-break); reason: the paper fixes no tie-break
--   - reading: B ⊂ A in heredity; S′ ⊂ S in the rank → ⊆; reason: "the size of the largest feasible subset in S" includes S
--   - encoding: S 2-approximates the revenue of Myerson's mechanism → R^M ≤ 2 R^S; reason: the definition of a 2-approximation
--   - encoding: the modification of S for distributions with point masses → omitted; reason: every distribution has a density, so the modification is never used
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Theorem 5, p. 6; mechanism S, §4, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsOptimal
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmActive
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmRevenue
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Theorem 5: for a matroid feasibility constraint, the sequential posted-price mechanism `S`
2-approximates the revenue of Myerson's mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, Theorem 5, p. 6 (PDF p. 8): "Let I be an instance of the BSMD with a matroid feasibility
constraint. Then, the mechanism S described above 2-approximates the revenue of Myerson's
mechanism for I." The mechanism `S` (§4, p. 6): "Let qi = q_i^M denote the probability that
Myerson's mechanism serves agent i, and let pi = Fi^{−1}(1 − qi) for all i. The SPM sets a price
of pi for agent i and offers to serve the agents in decreasing order of their prices."

Let `J` be a matroid on the agents `[n]`, values independent with regular distributions
`v_i ∼ μ i`, and `M` a revenue-optimal mechanism. Let `S` be the SPM that offers service to the
agents with `q_i^M > 0`, at prices `p_i = F_i^{−1}(1 − q_i^M)`, in decreasing order of price
(ties broken arbitrarily). Then `R^M ≤ 2 R^S`.

**Formalization Note.** Myerson's mechanism is replaced by any optimal admissible mechanism
(`IsOptimal`), which contains it by Theorem 19; `S` is built from that mechanism's allocation
probabilities. Regularity includes a positive density inside the support (`IsRegular`). Agents
with `q_i^M = 0` are not offered (in the paper they accept with probability `0`). Any order that
is non-increasing in price is allowed. -/
theorem theorem_5_matroid_spm {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (hreg : ∀ i, IsRegular (μ i))
    (M : Mechanism n) (hM : IsOptimal Feas μ M)
    (p : Fin n → ℝ) (hp : ∀ i ∈ spmActive μ M, IsQuantilePrice (μ i) (allocProb μ M i) (p i))
    (σ : Fin n ≃ Fin n) (hσ : IsDecreasingOrder p (spmActive μ M) σ) :
    revenue μ M ≤ 2 * spmRevenue Feas μ p (spmActive μ M) σ := by sorry

end SeqPostedPricing.MatroidSPM
