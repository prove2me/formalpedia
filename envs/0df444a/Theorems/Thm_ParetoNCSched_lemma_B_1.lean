-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_B_1
-- name    : ParetoNCSched.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:23:28.756201+00:00
-- url     : https://prove2.me/theorems/4de628ca-4d62-4678-bd95-0b5844c729e3
-- title:
--   Lemma B.1 — structure of the run of $\mathrm{MRC}_R$
-- statement:
--   Let $R\ge2$, let $p\in(0,\infty)^n$ and let $\sigma$ be any predicted order. Consider the run of $\mathrm{MRC}_R$ and a time $t<t_\infty$ at which $N(t)\ge2$ jobs are unfinished, with committed job $j$, waiting jobs $W$ and level $\ell$. Then:
--
--   1. (a) every waiting job has elapsed time $\ell$, and $e_j\ge\ell$; while a given job is the committed job, $e_j-\ell$ is strictly increasing; consequently every job $i$ with $e_i>e_j$, or with $i\ne j$ and $e_i>\ell$, is completed;
--   2. (b) in the mixing branch, $\gamma_c<N/R<\gamma_r$, so $a$ is well defined, $1/N<a<1$ and $b<1/N<a$;
--   3. each interval $[t_k,t_{k+1})$ with $N(t_k)\ge2$ is non-empty.
--
--   These structural facts make the rates $\gamma_c,\gamma_r$ count only completed jobs and keep $a\in(1/N,1)$, which Lemmas B.2 and B.3 use.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: "at every time t < t∞" → "t ∈ [t_k, t_{k+1}) for some k"; reason: t₀ = 0 and the event times are non-decreasing, so the union of these intervals is [0, t∞)
--   - encoding: the branch and the rates a, b "at time t" → the branch and a, b computed at the last event time t_k ≤ t (the state `run R p σ k`); γ_c, γ_r, N evaluated at the state at time t; reason: the algorithm computes them at t_k and uses them on [t_k, t_{k+1}) (p.17, p.24)
--   - encoding: "while a given job is the committed job, eⱼ − ℓ is strictly increasing" → for times t < t′ (both before t∞, N(t′) ≥ 2) with the same committed job j, eⱼ(t) − ℓ(t) < eⱼ(t′) − ℓ(t′); reason: a job that stops being committed has completed and is never committed again, so it is committed at every time between t and t′
--   - encoding: "t_{k+1} < ∞" → not stated separately; reason: event times are real numbers in the formalization, so finiteness is automatic
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
--   - encoding: "each interval [t_k, t_{k+1}) is non-empty" → for every k with N(t_k) ≥ 2; reason: p.17 defines the event intervals from states with N ≥ 2; with N ≤ 1 "there are no further events"
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma B.1, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_stateAt
import Definitions.Def_ParetoNCSched_committedJob
import Definitions.Def_ParetoNCSched_level
import Definitions.Def_ParetoNCSched_gammaC
import Definitions.Def_ParetoNCSched_gammaR
import Definitions.Def_ParetoNCSched_IsCommit
import Definitions.Def_ParetoNCSched_waitRate
import Definitions.Def_ParetoNCSched_eventTime
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma B.1 (Structure of the run).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, Lemma B.1, p.17: "For every instance and
every σ, at every time t < t∞ with N(t) ≥ 2: (a) the waiting jobs all have the same elapsed time ℓ,
and eⱼ ≥ ℓ; while a given job is the committed job, eⱼ − ℓ is strictly increasing. Consequently, the
jobs counted in γ_c and in γ_r are completed jobs; (b) in the mixing branch, γ_c < N/R < γ_r, so a is
well defined and 1/N < a < 1, and b < 1/N < a. Moreover each interval [t_k, t_{k+1}) is non-empty and
t_{k+1} < ∞." Standing assumption of Appendix B (p.17): R ≥ 2, σ arbitrary.

**Formalization Note.** "t < t∞" is `t ∈ [t_k, t_{k+1})` for some `k`. The state at `t` is
`stateAt`; the branch at `t` and the rates `a`, `b` are those computed at the event time `t_k`
(`run R p σ k`). The level is the minimum over the waiting jobs, so "same elapsed time ℓ" says every
waiting job attains it. `t_{k+1} < ∞` is automatic (times are real). -/
theorem lemma_B_1 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) :
    -- (a) and (b), at every time t < t∞ with N(t) ≥ 2
    (∀ (k : ℕ) (t : ℝ), t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1)) →
      2 ≤ (unfinished p (stateAt R p σ t)).card →
      ∀ j, committedJob p σ (stateAt R p σ t) = some j →
        (∀ g ∈ waiting p (stateAt R p σ t) j,
            (stateAt R p σ t).e g = level p (stateAt R p σ t) j) ∧
        level p (stateAt R p σ t) j ≤ (stateAt R p σ t).e j ∧
        (∀ i, ((stateAt R p σ t).e j < (stateAt R p σ t).e i ∨
              (i ≠ j ∧ level p (stateAt R p σ t) j < (stateAt R p σ t).e i)) →
            i ∉ unfinished p (stateAt R p σ t)) ∧
        (∀ j₀, committedJob p σ (run R p σ k) = some j₀ → ¬ IsCommit R p (run R p σ k) j₀ →
          gammaC (stateAt R p σ t) j < ((unfinished p (stateAt R p σ t)).card : ℝ) / R ∧
          ((unfinished p (stateAt R p σ t)).card : ℝ) / R < gammaR p (stateAt R p σ t) j ∧
          1 / ((unfinished p (stateAt R p σ t)).card : ℝ) < commitRate R p (run R p σ k) j₀ ∧
          commitRate R p (run R p σ k) j₀ < 1 ∧
          waitRate R p (run R p σ k) j₀ < 1 / ((unfinished p (stateAt R p σ t)).card : ℝ))) ∧
    -- (a) while a given job is the committed job, eⱼ − ℓ is strictly increasing
    (∀ (k k' : ℕ) (t t' : ℝ), t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1)) →
      t' ∈ Ico (eventTime R p σ k') (eventTime R p σ (k' + 1)) → t < t' →
      2 ≤ (unfinished p (stateAt R p σ t')).card →
      ∀ j, committedJob p σ (stateAt R p σ t) = some j →
        committedJob p σ (stateAt R p σ t') = some j →
        (stateAt R p σ t).e j - level p (stateAt R p σ t) j <
          (stateAt R p σ t').e j - level p (stateAt R p σ t') j) ∧
    -- each interval [t_k, t_{k+1}) is non-empty
    (∀ k : ℕ, 2 ≤ (unfinished p (run R p σ k)).card →
      eventTime R p σ k < eventTime R p σ (k + 1)) := by sorry

end ParetoNCSched
