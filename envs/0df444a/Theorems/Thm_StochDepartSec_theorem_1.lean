-- Prove2me | Theorems.Thm_StochDepartSec_theorem_1
-- name    : StochDepartSec.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:48.475985+00:00
-- url     : https://prove2.me/theorems/6adbc471-5111-480d-a8de-e01e99424a4c
-- title:
--   Theorem 1 — an optimal bivariate policy, monotone in $K_t$ and, for uniform arrivals, in $t$
-- statement:
--   Throughout, $n$ is the number of candidates, $\mathcal A$ is an arrival distribution with $\mathcal A([0,1])=1$ and $\mathcal L$ a waiting time distribution with $\mathcal L([0,\infty))=1$; no other assumption (atoms, continuity) is made on $\mathcal A$ or $\mathcal L$.
--
--   **Theorem 1.** There is a function $\Theta_n:\mathbb R\times\mathbb N\to\{0,1\}$ such that
--
--   1. the bivariate policy of $\Theta_n$ (when a candidate departs at time $t$, accept it iff it is the best-so-far and $\Theta_n(t,K_t)=1$) is optimal among all admissible policies;
--   2. for every $t\in[0,1]$, $k\mapsto\Theta_n(t,k)$ is non-decreasing on $\{1,\dots,n\}$;
--   3. if $\mathcal A$ is the uniform distribution on $[0,1]$, then for every $k\in\{1,\dots,n\}$, $t\mapsto\Theta_n(t,k)$ is non-increasing on $[0,1]$.
--
--   Here $0<1$ (reject $<$ accept). So the optimal stopping rule for hiring the best secretary when candidates arrive at random times and leave after random waiting times depends only on the current time and the number of arrivals so far; at a fixed time it accepts once enough candidates have arrived, and for uniform arrivals it becomes more reluctant over time.
--
--   Differences from the source:
--   - encoding: candidates indexed by arrival order, overall order a permutation π with π(i) = 1 the best → fixed labels Fin n and a uniform permutation σ with σ i = 0 the best; reason: a relabelling; labels are independent of the times and the order, and ranks are shifted by one
--   - generalization: policies decide from the history (a, d, r) at time t → admissible policies may also read the candidates' labels and an independent uniform seed u ∈ [0,1]; reason: the comparison class is larger; the paper's deterministic policies are the members constant in u and symmetric in labels, and the bivariate policy belongs to the paper's class, so the Lean statement implies the paper's
--   - encoding: a policy → a policy whose acceptance events are measurable; reason: the success probability of a policy is only defined when its success event is measurable
--   - reading: K_t, "arrived up to time t" / "arrived prior to t" (Definition 3) → K_t = #{i | a_i ≤ t}, arrivals at t counted; reason: §3.2 p.8 draws the future from A conditioned on (t, 1], which fixes the closed reading
--   - encoding: Θ_n : [0,1] × [n] → {0,1} → Θ : ℝ → ℕ → Bool, monotonicity asserted on [0,1] × {1,…,n}; reason: values off the paper's domain are never read on almost every outcome
--   - encoding: A uniform → A = Lebesgue measure restricted to [0, 1]; reason: the uniform distribution on [0, 1]
--   - encoding: probabilities → ENNReal measures converted with toReal; reason: all values are in [0,1]
--   - encoding: the algorithm irrevocably accepts or rejects each departing candidate and hires one candidate → a policy names at most one candidate per instant (Option (Fin n)), a candidate is accepted iff named at its own departure time, and success means the earliest accepted candidate is the best overall; reason: only the first acceptance is a hire, so neither later acceptances nor the choice among simultaneous departures beyond one changes any outcome
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, Theorem 1, p.6

import Mathlib
import Definitions.Def_StochDepartSec_bivariate
import Definitions.Def_StochDepartSec_Policy_IsOptimal
open MeasureTheory

namespace StochDepartSec

/-- Theorem 1: the stochastic departure secretary problem has an optimal policy that is bivariate,
i.e. given by a function `Θ_n(t, K_t)`; `Θ_n` is non-decreasing in `K_t` for fixed `t`, and, if
the arrival distribution is uniform on `[0, 1]`, non-increasing in `t` for fixed `K_t`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, Theorem 1, p.6: "There exists an optimal policy for the stochastic departure secretary problem
that is bivariate. The function Θ_n is non-decreasing in K_t for fixed t and if A is uniform it is
non-increasing in t for fixed K_t."

The instance: `n` candidates, arrival distribution `A` with `A [0,1] = 1` ("events only occur in the interval [0, 1]", §2, p.5), waiting time distribution `L` with `L [0,∞) = 1` ("a non-negative real number", §2, p.5); no other assumption on `A` or `L` ("The results of Section 3 all hold for arbitrary arrival distributions except for Lemma 12", p.5).

**Formalization Note** One `Θ` satisfies all three clauses. Optimality is against every
admissible policy (history-dependent, randomized through the seed, label-aware) and includes the
admissibility of the bivariate policy. `Θ` is a function on `ℝ × ℕ`; the monotonicity clauses
are asserted on the paper's domain `[0, 1] × [n]`, `[n] = {1, …, n}`. `Bool` is ordered by
`false < true` (reject < accept). "A is uniform" is `A = ` Lebesgue measure restricted to
`[0, 1]`. -/
theorem theorem_1 (n : ℕ) (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (hA : A (Set.Icc 0 1) = 1) (hL : L (Set.Ici 0) = 1) :
    ∃ Θ : ℝ → ℕ → Bool, (bivariate (n := n) Θ).IsOptimal A L ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, MonotoneOn (Θ t) (Set.Icc 1 n)) ∧
      (A = volume.restrict (Set.Icc (0 : ℝ) 1) →
        ∀ k ∈ Set.Icc 1 n, AntitoneOn (fun t => Θ t k) (Set.Icc (0 : ℝ) 1)) := by sorry

end StochDepartSec
