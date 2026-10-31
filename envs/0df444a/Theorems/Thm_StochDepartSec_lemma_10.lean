-- Prove2me | Theorems.Thm_StochDepartSec_lemma_10
-- name    : StochDepartSec.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:39.67357+00:00
-- url     : https://prove2.me/theorems/197f0fc8-dd15-4daf-a0e9-c4bcd5fc7ad7
-- title:
--   Lemma 10 — $V(t,k)\ge\frac{k}{k+1}V(t,k+1)$
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   **Lemma 10.** For every $t\in[0,1]$ and every $k\in\{1,\dots,n-1\}$,
--
--   $$
--   \Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k,\mathcal E_t]\ \ge\ \frac{k}{k+1}\,\Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k+1,\mathcal E_t],
--   $$
--
--   where $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid K_t=k,\mathcal E_t]$ is the value of rejecting $V(t,k)$. Rejecting with one arrival fewer loses at most the factor $k/(k+1)$. This is the inequality that makes the optimal policy monotone in the number of arrivals (Lemma 11).
--
--   Differences from the source:
--   - encoding: Pr[success(rej_t) | K_t = k, E_t] → rejValue n A L t k: sup over admissible policies that never accept a candidate arrived by t of P[success | K_t = k]; reason: E_t can have probability 0; on E_t, rej_t and pol_t have the same success probability (p.11) and given K_t = k the success of pol_t is independent of E_t (p.13); at P(K_t = k) = 0 the value is 0
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - encoding: the value of rejecting optimizes over policies that decide from the history (a, d, r) → rejValue optimizes over admissible policies that may also read labels and an independent seed; reason: labels and seed are independent of the times and the order, so they do not change the optimal conditional success probability
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Lemma 10, p.8

import Mathlib
import Definitions.Def_StochDepartSec_rejValue
open MeasureTheory

namespace StochDepartSec

/-- Lemma 10: the value of rejecting with `k` arrivals is at least `k/(k+1)` times the value of
rejecting with `k + 1` arrivals, at every time `t ∈ [0, 1]` and for every `k ∈ [n − 1]`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Lemma 10, p.8: "For any t ∈ [0, 1] and any k ∈ [n − 1], it holds that
Pr[success(rej_t) | K_t = k, E_t] ≥ k/(k + 1) Pr[success(rej_t) | K_t = k + 1, E_t]."

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** `Pr[success(rej_t) | K_t = k, E_t]` is `rejValue n A L t k` (see its
docstring). `[n − 1] = {1, …, n − 1}`. At states where `P(K_t = k) = 0` both sides are `0`, so no
nondegeneracy hypothesis is needed. -/
theorem lemma_10 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k ∈ Finset.Icc 1 (n - 1),
      ((k : ℝ) / (k + 1)) * rejValue n A L t (k + 1) ≤ rejValue n A L t k := by sorry

end StochDepartSec
