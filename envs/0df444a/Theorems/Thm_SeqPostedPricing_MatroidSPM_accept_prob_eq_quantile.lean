-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_accept_prob_eq_quantile
-- name    : SeqPostedPricing.MatroidSPM.accept_prob_eq_quantile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:04.384988+00:00
-- url     : https://prove2.me/theorems/7f145aaf-e97f-4d4f-bd5a-1b6d57c5d1fa
-- title:
--   §4: offered the price $F_i^{-1}(1-q_i)$, agent $i$ accepts with probability exactly $q_i$
-- statement:
--   Let $\nu$ be a regular value distribution and let $p=F^{-1}(1-q)$ be the quantile price for $q$. An agent with value $v\sim\nu$ that is offered the price $p$ accepts with probability exactly $q$:
--
--   $$
--   \Pr_{v\sim\nu}[v\ge p]=q .
--   $$
--
--   This identifies the acceptance probabilities of the sequential posted-price mechanism with the allocation probabilities of the benchmark mechanism.
--
--   Differences from the source:
--   - generalization: q_i = q_i^M, the allocation probability of Myerson's mechanism → any number q with a quantile price p; reason: Myerson's q_i^M is one such number
--   - encoding: agent i accepts → v ≥ p; reason: §1: a rational agent accepts iff the price is no more than its value
--   - reading: regular: φ(v) = v − (1 − F(v))/f(v) monotone non-decreasing → a density f with f > 0 wherever 0 < F < 1 and φ monotone on {0 < F < 1} (`IsRegular`); reason: φ is undefined where f = 0 and is read as −∞ there, so monotonicity rules out a density gap inside the support; under the other reading Lemma 2 fails (v ∼ ½U[0,1] + ½U[10,11], a mechanism posting 10 w.p. 0.9 and 0 w.p. 0.1 earns 4.5 > p q = 0.495)
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsRegular
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsQuantilePrice
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **An agent offered the price `F_i^{−1}(1 − q_i)` accepts with probability exactly `q_i`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8): "If offered service, agent i accepts with probability
exactly qi."

For a regular value distribution `ν` and a price `p` with `p = F^{−1}(1 − q)`
(`IsQuantilePrice ν q p`), the acceptance probability `Pr[v ≥ p]` equals `q`.

**Formalization Note.** The agent accepts when the price is at most its value (§1, p. 1), so the
acceptance event is `v ≥ p`. -/
theorem accept_prob_eq_quantile (ν : Measure ℝ) [IsProbabilityMeasure ν] (hreg : IsRegular ν)
    (q p : ℝ) (hp : IsQuantilePrice ν q p) : (ν (Set.Ici p)).toReal = q := by sorry

end SeqPostedPricing.MatroidSPM
