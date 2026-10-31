-- Prove2me | Theorems.Thm_StochDepartSec_observation_8
-- name    : StochDepartSec.observation_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:00.10199+00:00
-- url     : https://prove2.me/theorems/0f0fcf7e-3b5c-4db0-a8cd-a84f27f94189
-- title:
--   Observation 8 — accepting the best-so-far after $k$ arrivals succeeds with probability $k/n$
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   **Observation 8.** Fix a time $t$ and $k\in\mathbb N$. Let $H$ be a measurable event that is a union of histories until $t$ (if $\omega\in H$ and $\omega'$ has the same history until $t$, then $\omega'\in H$), such that in every outcome of $H$ exactly $k$ candidates have arrived by $t$ and a best-so-far candidate exists. Then
--
--   $$
--   \Pr\bigl[H\cap\{\text{the best-so-far at }t\text{ is the best overall}\}\bigr]=\frac kn\,\Pr[H].
--   $$
--
--   This is the paper's $\Pr[\mathrm{success}(\mathrm{acc}_t)\mid\mathrm{hist}_t=h]=k/n$, integrated over histories: accepting the departing best-so-far candidate after $k$ arrivals succeeds with probability $k/n$ whatever else the history contains.
--
--   Differences from the source:
--   - encoding: Pr[success(acc_t) | hist_t = h] = k/n for a single history h → P(H ∩ {best-so-far at t is best overall}) = (k/n)·P(H) for every measurable HistEq-closed event H; reason: a single history has probability 0 for continuous A; the integrated form is the meaning of the conditional probability
--   - generalization: histories in which a best-so-far candidate departs at time t → histories in which a best-so-far candidate exists at time t (departing or not); reason: events H contained in the departure event are a special case
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Observation 8, p.7

import Mathlib
import Definitions.Def_StochDepartSec_Outcome
import Definitions.Def_StochDepartSec_outcomeLaw
import Definitions.Def_StochDepartSec_numArrived
import Definitions.Def_StochDepartSec_BestSoFar
import Definitions.Def_StochDepartSec_HistEq
open MeasureTheory

namespace StochDepartSec

/-- Observation 8: given a history until `t` with `k` arrivals and a best-so-far candidate, the
best-so-far candidate is the best overall with conditional probability `k/n`. Stated without
conditioning on null events: for every measurable event `H` that is a union of histories until
`t` in each of which `k` candidates have arrived and a best-so-far candidate exists,
`P(H ∩ {the best-so-far at t is the best overall}) = (k/n) · P(H)`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Observation 8, p.7: "Given a time t, let h be a history until t in which k candidates have
arrived by time t and a best-so-far candidate departs at time t. Then
Pr[success(acc_t) | hist_t = h] = k/n."

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** `success(acc_t)` on such a history is the event that the best-so-far at
`t` is the best overall. "Conditioned on `hist_t = h`" is rendered by integrating over every
`HistEq t`-closed measurable event `H` (a single history has probability 0 for continuous `A`).
The departure of the best-so-far at `t` is not required in `H`; events `H` contained in it are a
special case. Probabilities are converted with `toReal`. -/
theorem observation_8 {n : ℕ} (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1)
    (t : ℝ) (k : ℕ) (H : Set (Outcome n)) (hHm : MeasurableSet H)
    (hHk : ∀ ω ∈ H, numArrived ω t = k ∧ ∃ i, BestSoFar ω t i)
    (hHhist : ∀ ω ω' : Outcome n, HistEq t ω ω' → ω ∈ H → ω' ∈ H) :
    (outcomeLaw n A L (H ∩ {ω | ∃ i, BestSoFar ω t i ∧ (rank ω i : ℕ) = 0})).toReal =
      ((k : ℝ) / n) * (outcomeLaw n A L H).toReal := by sorry

end StochDepartSec
