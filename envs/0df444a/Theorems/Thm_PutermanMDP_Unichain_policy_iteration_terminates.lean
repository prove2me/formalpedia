-- Prove2me | Theorems.Thm_PutermanMDP_Unichain_policy_iteration_terminates
-- name    : PutermanMDP.Unichain.policy_iteration_terminates
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:33.081992+00:00
-- url     : https://prove2.me/theorems/bd21bbcb-2b65-46c5-a26e-118172779fa4
-- title:
--   Theorem 8.6.6 — finite termination of unichain policy iteration
-- statement:
--   Let $M$ be a finite stationary Markov decision process with a nonempty state set and nonempty admissible action sets, and suppose every admissible deterministic stationary policy is unichain. Start with any admissible rule $d_0$. Policy iteration evaluates each rule by (8.6.1), chooses a maximizing rule by (8.6.2), retains the whole incumbent if it is still maximizing, and stops at the first equality of consecutive rules.
--
--   Runs exist from every $d_0$. For every run, with arbitrary choices of evaluation constants and maximizing rules allowed by those steps, there is a finite first stopping index $n$ such that
--   $$d_{n+1}=d_n,\qquad B(g_n,h_n)=0.$$
--   The returned stationary policy $(d_n)^\infty$ is average optimal against every admissible history-dependent randomized policy $\pi$:
--   $$g^{(d_n)^\infty}_-(s)\ge g^\pi_+(s)\quad\text{for all }s,\pi.$$
--   Its scalar evaluation value is the optimal gain under both criteria:
--   $$g_n=g^*_+(s)=g^*_-(s)\quad\text{for all }s.$$
--
--   This is finite termination of the actual policy iteration algorithm, including transient states, rather than just existence of an optimality-equation solution. Average rewards are limits of expected finite-horizon rewards per decision epoch.
--
--   Differences from the source:
--   - encoding: finite nonempty state set and finite nonempty state-dependent action sets → finite types S and A, Nonempty S, and nonempty admissible finsets; reason: the union of finitely many finite action sets is finite; irrelevant action entries can be extended by zero rewards and any stochastic row
--   - encoding: standing finite unichain model of §8.6 with bounded rewards → IsUnichain M and a finite stationary MDP; reason: finiteness makes the reward bound automatic; no irreducibility or aperiodicity is added
--   - encoding: policy iteration initialized at an arbitrary rule and stopped at its first adjacent equality → existence of infinite extensions of runs and a first finite stopping index for every such run; reason: continuation past stopping only represents a finite execution by a total sequence; it adds no assumption of termination
--   - encoding: a solution (g*,h) and an average optimal stationary policy → Bellman equality, expected liminf-versus-limsup optimality, and equality with both optimal gain functions; reason: these spell out the meanings of g* and average optimality in §8.1.2; evaluation vectors retain all permitted additive constants
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 383 (PDF 399), Theorem 8.6.6; algorithm p. 378 (PDF 394)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration
open MarkovDecisionProcesses

namespace PutermanMDP.Unichain

/-- Theorem 8.6.6 with every permitted evaluation solution and tie choice.
Runs exist from every initial rule, and every run reaches the exact step-4
stopping test with Bellman equality and optimality against all HR policies. -/
theorem policy_iteration_terminates {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M)
    (d₀ : Rule M) :
    (∃ (d : ℕ → Rule M) (g : ℕ → ℝ) (h : ℕ → S → ℝ),
      d 0 = d₀ ∧ IsRun M d g h) ∧
    (∀ (d : ℕ → Rule M) (g : ℕ → ℝ) (h : ℕ → S → ℝ),
      d 0 = d₀ → IsRun M d g h →
      ∃ n, StopsAt M d n ∧
        (∀ s, optimalityResidual M (g n) (h n) s = 0) ∧
        IsAverageOptimal (stationaryPolicy M (d n).val (d n).property) ∧
        (∀ s, optGainSup M s = g n ∧ optGainInf M s = g n)) := by sorry

end PutermanMDP.Unichain
