-- Prove2me | Theorems.Thm_StochDepartSec_lemma_11
-- name    : StochDepartSec.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:57.394058+00:00
-- url     : https://prove2.me/theorems/e232f8ad-dee6-46a7-8762-95541bff101e
-- title:
--   Lemma 11 — the optimal $\Theta_n$ is non-decreasing in $K_t$
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   Let $\Theta^{\mathrm{lazy}}(t,k)=1$ iff $V(t,k)<k/n$ be the decision function of the optimal lazy policy (Lemma 9).
--
--   **Lemma 11.** For every $t\in[0,1]$, the map $k\mapsto\Theta^{\mathrm{lazy}}(t,k)$ is non-decreasing on $\{1,\dots,n\}$ (with reject $<$ accept): at a fixed time the optimal policy rejects below some number of arrivals and accepts above it.
--
--   Differences from the source:
--   - reading: opt, the unique optimal lazy policy → the bivariate policy of lazyRule (accept iff rejValue(t, K_t) < K_t/n); reason: Observation 7 with Observation 8 gives opt's decision at a departing best-so-far candidate as exactly this comparison
--   - encoding: Pr[success(rej_t) | K_t = k, E_t] → rejValue n A L t k: sup over admissible policies that never accept a candidate arrived by t of P[success | K_t = k]; reason: E_t can have probability 0; on E_t, rej_t and pol_t have the same success probability (p.11) and given K_t = k the success of pol_t is independent of E_t (p.13); at P(K_t = k) = 0 the value is 0
--   - encoding: Θ_n : [0,1] × [n] → {0,1} → Θ : ℝ → ℕ → Bool, monotonicity asserted on [0,1] × {1,…,n}; reason: values off the paper's domain are never read on almost every outcome
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - encoding: the value of rejecting optimizes over policies that decide from the history (a, d, r) → rejValue optimizes over admissible policies that may also read labels and an independent seed; reason: labels and seed are independent of the times and the order, so they do not change the optimal conditional success probability
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Lemma 11, p.9

import Mathlib
import Definitions.Def_StochDepartSec_lazyRule
open MeasureTheory

namespace StochDepartSec

/-- Lemma 11: the optimal policy's `Θ_n` is non-decreasing in `K_t`: for every `t ∈ [0, 1]`,
`k ↦ lazyRule n A L t k` is monotone on `{1, …, n}` (reject below some number of arrivals,
accept above).
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Lemma 11, p.9: "For any number of candidates n, time t, arrival distribution A and waiting
time distribution L, the optimal policy's Θ_n function is monotone non-decreasing in K_t."

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** The optimal policy's `Θ_n` is `lazyRule n A L` (Lemma 9). `Bool` is ordered
by `false < true` (reject < accept). -/
theorem lemma_11 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, MonotoneOn (lazyRule n A L t) (Set.Icc 1 n) := by sorry

end StochDepartSec
