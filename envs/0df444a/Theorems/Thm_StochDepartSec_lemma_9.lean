-- Prove2me | Theorems.Thm_StochDepartSec_lemma_9
-- name    : StochDepartSec.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:06.251606+00:00
-- url     : https://prove2.me/theorems/e72ec0fa-ed23-4a51-9aea-43461370269e
-- title:
--   Lemma 9 — the optimal lazy policy is bivariate
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   Let $V(t,k)$ be the value of rejecting at time $t$ with $k$ arrivals (the paper's $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k,\mathcal E_t]$) and let $\Theta^{\mathrm{lazy}}(t,k)=1$ iff $V(t,k)<k/n$.
--
--   **Lemma 9.** The bivariate policy of $\Theta^{\mathrm{lazy}}$, which accepts a departing best-so-far candidate at time $t$ iff $\Theta^{\mathrm{lazy}}(t,K_t)=1$, is optimal: it is admissible, and no admissible policy has a larger success probability.
--
--   This is the paper's statement that the optimal lazy policy's decisions depend only on the time $t$ and on $K_t$: by Observation 7 the optimal lazy policy accepts a departing best-so-far candidate iff $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid\mathrm{hist}_t=h]<\Pr[\mathrm{success}(\mathrm{acc}_t)\mid\mathrm{hist}_t=h]$, by Observation 8 the right side is $k/n$, and by Lemma 9 the left side depends on $h$ only through $(t,K_t)$.
--
--   Differences from the source:
--   - reading: opt, the unique optimal lazy policy → the bivariate policy of lazyRule (accept iff rejValue(t, K_t) < K_t/n); reason: Observation 7 with Observation 8 gives opt's decision at a departing best-so-far candidate as exactly this comparison
--   - encoding: Pr[success(rej_t) | K_t = k, E_t] → rejValue n A L t k: sup over admissible policies that never accept a candidate arrived by t of P[success | K_t = k]; reason: E_t can have probability 0; on E_t, rej_t and pol_t have the same success probability (p.11) and given K_t = k the success of pol_t is independent of E_t (p.13); at P(K_t = k) = 0 the value is 0
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - generalization: policies decide from the history (a, d, r) at time t → admissible policies may also read the candidates' labels and an independent uniform seed u ∈ [0,1]; reason: the comparison class is larger; the paper's deterministic policies are the members constant in u and symmetric in labels, and the bivariate policy belongs to the paper's class, so the Lean statement implies the paper's
--   - encoding: a policy → a policy whose acceptance events are measurable; reason: the success probability of a policy is only defined when its success event is measurable
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Lemma 9 with Observations 7 and 8, p.7

import Mathlib
import Definitions.Def_StochDepartSec_bivariate
import Definitions.Def_StochDepartSec_Policy_IsOptimal
import Definitions.Def_StochDepartSec_lazyRule
open MeasureTheory

namespace StochDepartSec

/-- Lemma 9 (with Observations 7 and 8): the optimal lazy policy is bivariate. The bivariate
policy that accepts the departing best-so-far candidate at time `t` with `K_t = k` arrivals iff
`rejValue(t, k) < k/n` is optimal among all admissible policies.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Lemma 9, p.7: "Given n, the arrival distribution A and waiting time distribution L, the optimal
lazy policy can be described by a bivariate function. That is, the decisions depend only on the time
t and K_t, the number of candidates that have arrived until time t." Observation 7, p.7: "opt
accepts this candidate if and only if it has not accepted any candidate before and
Pr[success(rej_t) | hist_t = h] < Pr[success(acc_t) | hist_t = h]"; Observation 8:
"Pr[success(acc_t) | hist_t = h] = k/n".

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** The optimal lazy policy's decision function is `lazyRule` (Observation 7
with Observation 8: accept iff `Pr[success(rej_t) | K_t = k, E_t] < k/n`, the left side being
`rejValue`). Optimality includes admissibility, hence measurability of the acceptance events. -/
theorem lemma_9 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1) :
    (bivariate (n := n) (lazyRule n A L)).IsOptimal A L := by sorry

end StochDepartSec
