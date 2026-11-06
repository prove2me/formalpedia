-- Prove2me | Theorems.Thm_ParetoNCSched_lemma_B_3
-- name    : ParetoNCSched.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:24:55.382415+00:00
-- url     : https://prove2.me/theorems/f1a9eb55-ec69-4a97-ac0b-c280e4a90bca
-- title:
--   Lemma B.3 — $O(n^2)$ events; $\Phi$ and $D$ affine between events
-- statement:
--   Let $R\ge2$. There is an absolute constant $C$ such that for every instance $p\in(0,\infty)^n$ and every predicted order $\sigma$, the run of $\mathrm{MRC}_R$ has at most $Cn^2$ events: there is an index $K\le Cn^2$ such that at most one job is unfinished at $t_K$, at least two are unfinished at every earlier event time, and the run is constant after the final completion; every time $t\ge0$ with $N(t)\ge2$ lies in $[t_k,t_{k+1})$ for some $k<K$, so Lemmas B.1 and B.2 apply there. Moreover:
--
--   1. (a) on every interval $[t_k,t_{k+1})$ between consecutive events, the committed job, $N$, $\gamma_c$ and $\gamma_r$ are constant and equal to their values at $t_k$, and $\Phi(e(t))$ is affine, with slope $\gamma_c$ in the commit branch and $N/R$ in the mixing branch; hence $D'=N-R\gamma_c$ in the commit branch and $D'=0$ in the mixing branch;
--   2. (b) at the last event time $t_K$ at most one job is unfinished; if job $j$ is, it runs alone at rate $1$ on $[t_K, t_K+p_j-e_j(t_K))$ and completes at $t_K+p_j-e_j(t_K)$.
--
--   Lemma B.3 shows that the run is well defined at all times and reduces the robustness proof to a finite induction over intervals.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - reading: "the run of MRC_R has O(n²) events and is defined at all times, so t∞ is the last event time" → one constant C, uniform in R ≥ 2 and in the instance, and an index K ≤ C n² with N(t_K) ≤ 1, N(t_k) ≥ 2 for k < K, and the run constant after the final completion; reason: the event count of the proof (p.19, Step 2) depends on n only; existence of K is what "defined at all times" asserts
--   - encoding: "Φ(e(t)) is affine with slope …; D′ = …" → explicit affine formulas on [t_k, t_{k+1}) anchored at the state at time t_k; reason: an affine function on an interval is determined by its value at t_k and its slope
--   - reading: "N, γ_c and γ_r are constant" between events → the committed job is also asserted constant on [t_k, t_{k+1}), and γ_c, γ_r are evaluated with it; reason: γ_c and γ_r are defined relative to the committed job; it changes only at a completion, which is an event
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
--   - encoding: "Lemmas B.1 and B.2 apply at every time with N(t) ≥ 2" → every t ≥ 0 with N(t) ≥ 2 lies in [t_k, t_{k+1}) for some k < K; reason: that interval membership is the time hypothesis of lemma_B_1 and lemma_B_2; time starts at 0 in the model (p.7)
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Lemma B.3, p.19

import Mathlib
import Definitions.Def_ParetoNCSched_stateAt
import Definitions.Def_ParetoNCSched_committedJob
import Definitions.Def_ParetoNCSched_gammaC
import Definitions.Def_ParetoNCSched_gammaR
import Definitions.Def_ParetoNCSched_IsCommit
import Definitions.Def_ParetoNCSched_eventTime
import Definitions.Def_ParetoNCSched_mrcRate
import Definitions.Def_ParetoNCSched_complTime
import Definitions.Def_ParetoNCSched_slack
import Definitions.Def_ParetoNCSched_Phi
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Lemma B.3 (Events).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, Lemma B.3, p.19: "For every instance and every σ, the run
of MRC_R has O(n²) events and is defined at all times, so t∞ is the last event time; in particular
Lemmas B.1 and B.2 apply at every time with N(t) ≥ 2. Moreover: (a) between consecutive events, N,
γ_c and γ_r are constant, and Φ(e(t)) is affine, with slope γ_c in the commit branch and N/R in the
mixing branch. Hence D′ = N − Rγ_c in the commit branch and D′ = 0 in the mixing branch; (b) at the
last event time at most one job is unfinished; if one is, it runs alone until it completes."
Standing assumption (p.17): R ≥ 2.

**Formalization Note.**
* O(n²): one constant `C`, uniform in `R ≥ 2` and in the instance, such that the index `K` of the
  last event satisfies `K ≤ C n²`. `K` is the first index with at most one unfinished job; every
  earlier state has `N ≥ 2`; after the final completion (index `K + 1`) the run is constant.
* "Lemmas B.1 and B.2 apply at every time with N(t) ≥ 2": every `t ≥ 0` with `N(t) ≥ 2` lies in
  `[t_k, t_{k+1})` for some `k < K`, the form of the time hypothesis of those two lemmas.
* (a): on `[t_k, t_{k+1})` with `N(t_k) ≥ 2`, the committed job, `N`, `γ_c`, `γ_r` at time `t` equal
  their values at `t_k`; `Φ(e(t))` and `D(t)` are affine in `t` with the stated slopes (`D` and
  `Φ(e(·))` anchored at the state of the run at time `t_k`).
* (b): if job `j` is unfinished at `t_K`, the rate function is "`j` alone at rate 1" on
  `[t_K, t_K + pⱼ − eⱼ(t_K))` and `j` completes at `t_K + pⱼ − eⱼ(t_K)`. -/
theorem lemma_B_3 :
    ∃ C : ℕ, ∀ (R : ℝ), 2 ≤ R → ∀ {n : ℕ} (p : Fin n → ℝ), (∀ j, 0 < p j) →
      ∀ σ : Equiv.Perm (Fin n), ∃ K : ℕ, K ≤ C * n ^ 2 ∧
        (unfinished p (run R p σ K)).card ≤ 1 ∧
        (∀ k < K, 2 ≤ (unfinished p (run R p σ k)).card) ∧
        (∀ m : ℕ, run R p σ (K + 1 + m) = run R p σ (K + 1)) ∧
        -- every time with N(t) ≥ 2 lies before t_K, so Lemmas B.1 and B.2 apply there
        (∀ t : ℝ, 0 ≤ t → 2 ≤ (unfinished p (stateAt R p σ t)).card →
          ∃ k < K, t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1))) ∧
        -- (a) between consecutive events
        (∀ k < K, ∀ j, committedJob p σ (run R p σ k) = some j →
          ∀ t ∈ Ico (eventTime R p σ k) (eventTime R p σ (k + 1)),
            committedJob p σ (stateAt R p σ t) = some j ∧
            (unfinished p (stateAt R p σ t)).card = (unfinished p (run R p σ k)).card ∧
            gammaC (stateAt R p σ t) j = gammaC (run R p σ k) j ∧
            gammaR p (stateAt R p σ t) j = gammaR p (run R p σ k) j ∧
            (IsCommit R p (run R p σ k) j →
              Phi (stateAt R p σ t).e = Phi (stateAt R p σ (eventTime R p σ k)).e +
                gammaC (run R p σ k) j * (t - eventTime R p σ k) ∧
              slack R (stateAt R p σ t) = slack R (stateAt R p σ (eventTime R p σ k)) +
                (((unfinished p (run R p σ k)).card : ℝ) - R * gammaC (run R p σ k) j) *
                  (t - eventTime R p σ k)) ∧
            (¬ IsCommit R p (run R p σ k) j →
              Phi (stateAt R p σ t).e = Phi (stateAt R p σ (eventTime R p σ k)).e +
                ((unfinished p (run R p σ k)).card : ℝ) / R * (t - eventTime R p σ k) ∧
              slack R (stateAt R p σ t) = slack R (stateAt R p σ (eventTime R p σ k)))) ∧
        -- (b) after the last event
        (∀ j ∈ unfinished p (run R p σ K),
          (∀ t ∈ Ico (eventTime R p σ K) (eventTime R p σ K + (p j - (run R p σ K).e j)),
            mrcRate R p σ t = Pi.single j 1) ∧
          complTime p (mrcRate R p σ) j =
            ENNReal.ofReal (eventTime R p σ K + (p j - (run R p σ K).e j))) := by sorry

end ParetoNCSched
