-- Prove2me | Theorems.Thm_StochDepartSec_lemma_12
-- name    : StochDepartSec.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:21.418634+00:00
-- url     : https://prove2.me/theorems/03ea1148-8d8d-4f68-b5d5-5c8dd4c8ff4b
-- title:
--   Lemma 12 — for uniform arrivals the optimal $\Theta_n$ is non-increasing in $t$
-- statement:
--   Let $n$ be the number of candidates, $\mathcal A$ the uniform distribution on $[0,1]$, and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$ and no other assumption. Let $\Theta^{\mathrm{lazy}}(t,k)=1$ iff $V(t,k)<k/n$ be the decision function of the optimal lazy policy (Lemma 9).
--
--   **Lemma 12.** For every $k$ and all $0\le t'\le t\le1$ with $\Pr[K_t=k]>0$: if $\Theta^{\mathrm{lazy}}(t,k)=1$ then $\Theta^{\mathrm{lazy}}(t',k)=1$. That is, with $K_t$ fixed, the optimal policy accepts early and rejects late: $\Theta_n$ is non-increasing in $t$.
--
--   The paper's sentence on p.7 announcing Lemma 12 as "monotone non-decreasing in $t$" is a typo; Theorem 1, Lemma 12 and its proof, and Example 5 all say non-increasing.
--
--   Differences from the source:
--   - encoding: for all t' ≤ t and K_t → for all 0 ≤ t' ≤ t ≤ 1 and k with P(K_t = k) > 0; reason: the condition excludes only the states (t = 1, k < n), (t = 0, k ≥ 1) and k > n, where K_t = k has probability 0 and the paper's conditional probability is undefined (rejValue is 0 there by convention); the goal theorem has no such condition
--   - encoding: A uniform → A = Lebesgue measure restricted to [0, 1]; reason: the uniform distribution on [0, 1]
--   - reading: opt, the unique optimal lazy policy → the bivariate policy of lazyRule (accept iff rejValue(t, K_t) < K_t/n); reason: Observation 7 with Observation 8 gives opt's decision at a departing best-so-far candidate as exactly this comparison
--   - encoding: Pr[success(rej_t) | K_t = k, E_t] → rejValue n A L t k: sup over admissible policies that never accept a candidate arrived by t of P[success | K_t = k]; reason: E_t can have probability 0; on E_t, rej_t and pol_t have the same success probability (p.11) and given K_t = k the success of pol_t is independent of E_t (p.13); at P(K_t = k) = 0 the value is 0
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - encoding: the value of rejecting optimizes over policies that decide from the history (a, d, r) → rejValue optimizes over admissible policies that may also read labels and an independent seed; reason: labels and seed are independent of the times and the order, so they do not change the optimal conditional success probability
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Lemma 12, p.10

import Mathlib
import Definitions.Def_StochDepartSec_outcomeLaw
import Definitions.Def_StochDepartSec_numArrived
import Definitions.Def_StochDepartSec_lazyRule
open MeasureTheory

namespace StochDepartSec

/-- Lemma 12: for uniform arrivals the optimal policy's `Θ_n` is non-increasing in `t`: if it
accepts at time `t` with `k` arrivals, it accepts at every earlier time `t' ∈ [0, t]` with `k`
arrivals.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Lemma 12, p.10: "If the arrival distribution is uniform, then for any number of candidates n,
number of candidates that have arrived so far K_t and waiting time distribution L, the optimal
policy's bivariate function Θ_n is monotone non-increasing in t."

The instance: `n` candidates, `A` the uniform distribution on `[0, 1]` (Lebesgue measure restricted
to `[0, 1]`), waiting time distribution `L` with `L [0,∞) = 1` and no other assumption.

**Formalization Note** The optimal policy's `Θ_n` is `lazyRule n A L` (Lemma 9). The hypothesis
`0 < P(K_t = k)` at the later time excludes exactly the states `t = 1`, `k < n`; `t = 0`, `k ≥ 1`;
and `k > n`, where `K_t = k` has probability 0, the paper's conditional probability is undefined,
and `rejValue` takes the value `0`. The paper's sentence on p.7 "(3) the optimal policy is
monotone non-decreasing in t for uniform arrivals (Lemma 12)" is a typo for non-increasing
(Theorem 1, Lemma 12 and its proof, Example 5). -/
theorem lemma_12 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hAu : A = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hL : L (Set.Ici 0) = 1) :
    ∀ (k : ℕ) (t' t : ℝ), 0 ≤ t' → t' ≤ t → t ≤ 1 →
      0 < outcomeLaw n A L {ω | numArrived ω t = k} →
      lazyRule n A L t k = true → lazyRule n A L t' k = true := by sorry

end StochDepartSec
