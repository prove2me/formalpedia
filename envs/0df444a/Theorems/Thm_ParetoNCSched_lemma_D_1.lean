-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_D_1
-- name    : ParetoNCSched.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:26:44.470512+00:00
-- url     : https://prove2.me/theorems/93e62c27-c828-4bc3-8bab-f1c53bb416cd
-- title:
--   Lemma D.1 — $\mathrm{MRC}_R$ on a correct order
-- statement:
--   Let $R\ge2$, $p\in(0,\infty)^n$ and let $\sigma$ be a correct order; write job $\sigma(k)$ for the $(k+1)$-st job of the order. In the run of $\mathrm{MRC}_R$:
--
--   1. (a) the jobs complete (with finite completion times) in the order $\sigma(0),\dots,\sigma(n-1)$, at distinct times; hence, while $\sigma(k)$ is the committed job, the unfinished jobs are exactly $\sigma(k),\dots,\sigma(n-1)$ and $N=n-k$;
--   2. (b) let $t_f$ be the first time with $N(t_f)\le1$ (it is attained and is an event time), and let $\ell(t)=e_{\sigma(n-1)}(t)$ for $t\le t_f$ and $\ell(t)=e_{\sigma(n-1)}(t_f)$ for $t\ge t_f$. Then $\ell$ is continuous and non-decreasing on $[0,\infty)$, $\ell(0)=0$, and while $N\ge2$ it is the level of Appendix B. The level rises only in the mixing branch: it is constant on every commit-branch interval $[t_k,t_{k+1})$. At every time, the unfinished jobs other than the committed job have elapsed time $\ell(t)$, and the committed job has elapsed time at least $\ell(t)$.
--
--   On a correct order the run therefore alternates between committing to the next job of the order and Round-Robin among the remaining jobs at a common level.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: "the relabelled instance" (σ the identity, p₁ ≤ ⋯ ≤ pₙ) and job i → σ kept, job i written σ(i − 1), N = n − k while σ(k) is committed; reason: relabelling only
--   - encoding: "t_f the first time with N(t_f) ≤ 1 (an event time)" → the infimum t_f of these times, with the conclusions that N(t_f) ≤ 1, N(t) ≥ 2 for t < t_f, and t_f is an event time; reason: states the existence that "the first time" presupposes
--   - encoding: "the level rises only in the mixing branch" → ℓ is constant on every interval [t_k, t_{k+1}) whose branch is the commit branch; reason: the branch at time t is the branch chosen at t_k (p.24)
--   - encoding: times t (continuity, monotonicity, "at every time") → t ≥ 0; reason: time starts at 0 in the model (p.7)
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma D.1, p.21

import Mathlib
import Definitions.Def_ParetoNCSched_levelD
import Definitions.Def_ParetoNCSched_IsCorrect
import Definitions.Def_ParetoNCSched_IsCommit
import Definitions.Def_ParetoNCSched_level
import Definitions.Def_ParetoNCSched_eventTime
import Definitions.Def_ParetoNCSched_complTime
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma D.1 (MRC_R on a correct order).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, Lemma D.1, p.21: "Let R ≥ 2 and
consider the run of MRC_R on the relabelled instance. (a) The jobs complete in the order 1, . . . , n,
at distinct times. Hence, while job i is the committed job, the unfinished jobs are exactly
i, i + 1, . . . , n, and N = n − i + 1. (b) Let t_f be the first time with N(t_f) ≤ 1 (an event time,
by Lemma B.3(b)), and define the level by ℓ(t) = eₙ(t) for t ≤ t_f and ℓ(t) = ℓ_f := eₙ(t_f) for
t ≥ t_f. Then ℓ is continuous and non-decreasing, ℓ(0) = 0, and while N ≥ 2 it is the level ℓ of
Appendix B. The level rises only in the mixing branch. At every time, the unfinished jobs other than
the committed job have elapsed time ℓ(t), and the committed job, if any, has elapsed time at least
ℓ(t)."

**Formalization Note.** "The relabelled instance" (p.20): σ is correct and job `i` (1-based) is
`σ (i − 1)`; so job `σ k` completes before `σ k'` for `k < k'`, and while `σ k` is committed the
unfinished jobs are the `σ k'` with `k' ≥ k`, `N = n − k`. `t_f` is `firstSingleTime` (asserted to be
attained and an event time); `ℓ` is `levelD`; times are `t ≥ 0`. "Rises only in the mixing branch":
`ℓ` is constant on every interval `[t_k, t_{k+1})` whose branch is the commit branch. -/
theorem lemma_D_1 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) (hσ : IsCorrect p σ) :
    -- (a)
    (∀ k : Fin n, complTime p (mrcRate R p σ) (σ k) < ⊤) ∧
    (∀ k k' : Fin n, k < k' →
      complTime p (mrcRate R p σ) (σ k) < complTime p (mrcRate R p σ) (σ k')) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ k : Fin n, committedJob p σ (stateAt R p σ t) = some (σ k) →
      unfinished p (stateAt R p σ t) = Finset.univ.filter (fun i => k ≤ σ.symm i) ∧
      (unfinished p (stateAt R p σ t)).card = n - (k : ℕ)) ∧
    -- (b) the time t_f
    (0 ≤ firstSingleTime R p σ ∧
      (unfinished p (stateAt R p σ (firstSingleTime R p σ))).card ≤ 1 ∧
      (∀ t : ℝ, 0 ≤ t → t < firstSingleTime R p σ → 2 ≤ (unfinished p (stateAt R p σ t)).card) ∧
      ∃ k : ℕ, eventTime R p σ k = firstSingleTime R p σ) ∧
    -- (b) the level
    ContinuousOn (levelD R p σ) (Ici 0) ∧ MonotoneOn (levelD R p σ) (Ici 0) ∧
    levelD R p σ 0 = 0 ∧
    (∀ t : ℝ, 0 ≤ t → 2 ≤ (unfinished p (stateAt R p σ t)).card →
      ∀ j, committedJob p σ (stateAt R p σ t) = some j →
        levelD R p σ t = level p (stateAt R p σ t) j) ∧
    (∀ (k : ℕ) (j : Fin n), 2 ≤ (unfinished p (run R p σ k)).card →
      committedJob p σ (run R p σ k) = some j → IsCommit R p (run R p σ k) j →
      ∀ t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1)),
        levelD R p σ t = levelD R p σ (eventTime R p σ k)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ j, committedJob p σ (stateAt R p σ t) = some j →
      (∀ i ∈ unfinished p (stateAt R p σ t), i ≠ j → (stateAt R p σ t).e i = levelD R p σ t) ∧
      levelD R p σ t ≤ (stateAt R p σ t).e j) := by sorry

end ParetoNCSched
