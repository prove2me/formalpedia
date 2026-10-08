-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_observation_2_4
-- name    : StochSchedPrec.CMNS.observation_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:20.859186+00:00
-- url     : https://prove2.me/theorems/a6f3733b-4425-4f16-b3d1-e579f68d575d
-- title:
--   Observation 2.4, p. 794 — CMNS charges each job at most βE[P_j], charges in [r_j(p), S_j(p)[ go to B_j, and no deliberate idle time is uncharged
-- statement:
--   Consider an instance with $m\ge1$ machines, acyclic precedence constraints and release dates $r_j\ge0$ satisfying Assumption 2.1 ($r_i\le r_j$ whenever $i$ is a predecessor of $j$). Let $L$ be a priority list, $\beta\ge0$, $\mu_j\ge0$ (the expected processing times $\mathrm E[P_j]$ in the paper), $p\ge0$ a realization, and $S$ the schedule constructed by Algorithm CMNS. Then for every job $j$:
--   1. job $j$ is charged no more than $\beta\mu_j$ deliberate idle time: $\mathrm{charge}_j(t)\le\beta\mu_j$ for all $t$;
--   2. the deliberate idle time in $[r_j(p),S_j(p)[$ is charged only to jobs in $B_j$: a job deliberately delayed at a time $t\in[r_j(p),S_j(p)[$ lies in $B_j$;
--   3. there is no uncharged deliberate idle time: whenever a machine is idle at $t$ while some job of the residual list is available, some job is deliberately delayed at $t$, so the idle machines' time is charged to it.
--
--   These three facts are what the completion-time bound of Lemma 2.5 uses about the algorithm.
--
--   **Formalization Note** The paper states the observation for $\mu_j=\mathrm E[P_j]$; the statement here holds for every nonnegative threshold vector $\mu$, since the algorithm uses $\mathrm E[P_j]$ only through the threshold. Assumption 2.1 is the standing assumption of §2 and is carried as a hypothesis.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 794, Observation 2.4

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem observation_2_4 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (β : ℝ) (hβ : 0 ≤ β) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) :
    (∀ (j : V) (t : ℝ), charge m A r L p S j t ≤ β * μ j) ∧
    (∀ (j : V) (t : ℝ), availTime A r p S j ≤ t → t < S j →
      ∀ k, IsDelayed A r L p S k t → k ∈ before L j) ∧
    (∀ t : ℝ, busy p S t < m → (∃ i, t < S i ∧ avail A r p S i t) →
      ∃ k, IsDelayed A r L p S k t) := by sorry

end StochSchedPrec.CMNS
