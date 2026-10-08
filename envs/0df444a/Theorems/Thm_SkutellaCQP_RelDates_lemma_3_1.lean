-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_lemma_3_1
-- name    : SkutellaCQP.RelDates.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:14.826357+00:00
-- url     : https://prove2.me/theorems/7c6c06a7-349a-4e27-a266-1d3c424b8a9a
-- title:
--   Lemma 3.1, p. 15 — some optimal schedule sequences every time slot by ≺ᵢ without interruption
-- statement:
--   Consider an instance of $R \mid r_{ij} \mid \sum w_jC_j$ with $m \ge 1$ machines, processing times $p_{ij} > 0$, weights $w_j \ge 0$ and release dates $r_{ij} \ge 0$. Then there is an optimal schedule in which the jobs of every time slot $i_k$ are sequenced according to $\prec_i$ without interruption. That is, there is a feasible nonpreemptive schedule $S$ such that
--
--   1. $\sum_j w_jC_j(S) \le \sum_j w_jC_j(S')$ for every feasible schedule $S'$, and
--   2. whenever $j \ne j'$ lie in the same time slot $i_k$ and $j \prec_i j'$, job $j$ starts before $j'$; if moreover no job $j''$ of that slot satisfies $j \prec_i j'' \prec_i j'$, then $j'$ starts exactly at the completion time of $j$.
--
--   This lemma reduces the scheduling problem to an assignment of jobs to time slots: the order inside a slot is fixed by Smith's ratio rule.
--
--   **Formalization Note.** This is the second sentence of Lemma 3.1 ("there exists an optimal solution where the jobs are sequenced according to $\prec_i$ in each time slot"), together with "without interruption" from the first. The first sentence, read as a statement about *every* optimal schedule, fails when some $w_j = 0$ (idling before a zero-weight job costs nothing), so it is not formalized. The existence of an optimal schedule is part of the page's claim and is part of the conclusion. The hypothesis $m \ge 1$ is added: with no machine and $n \ge 1$ jobs there is no schedule at all.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 15, Lemma 3.1

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Lemma 3.1, p. 15 (second sentence, with "without interruption" from the first): there is
an optimal schedule in which the jobs of every time slot are sequenced by `≺_i` back to back. -/
theorem lemma_3_1 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (hm : 0 < m) :
    ∃ S : Sched m n, SFeasible p r S ∧ (∀ S' : Sched m n, SFeasible p r S' → sval p w S ≤ sval p w S') ∧
      SlotSequenced p w r S := by sorry

end SkutellaCQP.RelDates
