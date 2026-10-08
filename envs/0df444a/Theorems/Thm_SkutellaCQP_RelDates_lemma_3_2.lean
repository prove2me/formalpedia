-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_lemma_3_2
-- name    : SkutellaCQP.RelDates.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:23.078013+00:00
-- url     : https://prove2.me/theorems/f4807a85-ce7a-4533-b582-ad12190e4624
-- title:
--   Lemma 3.2, p. 16 — rebuilding a slot-sequenced schedule from its slot assignment gives a slot-sequenced schedule that delays no job
-- statement:
--   Let $S$ be a feasible nonpreemptive schedule for $R \mid r_{ij} \mid \sum w_jC_j$ whose time slots are sequenced by $\prec_i$ without interruption (the property of Lemma 3.1), and let $\tau$ be its assignment of jobs to time slots ($j \in i_k$ if $j$ is started on machine $i$ within $[\rho_{i_k}, \rho_{i_{k+1}})$). Then
--
--   1. $\tau$ is a feasible slot assignment ($\rho_{i_k} \ge r_{ij}$ whenever $j \in i_k$);
--   2. the schedule reconstructed from $\tau$ (each slot sequenced by $\prec_i$, slot starts (15)–(16)) is a feasible nonpreemptive schedule;
--   3. the reconstructed schedule again has the property of Lemma 3.1: in each of its time slots the jobs are sequenced by $\prec_i$ without interruption; and
--   4. for every job $j$, the completion time (17) of $j$ in the reconstructed schedule is at most its completion time in $S$:
--   $$C_j(\tau) \le C_j(S).$$
--
--   Applied to the optimal schedule of Lemma 3.1, this is Lemma 3.2: since $w \ge 0$, item 4 gives $\sum_j w_jC_j(\tau) \le \sum_j w_jC_j(S)$, so the schedule reconstructed from the slot assignment is again optimal, and by item 3 it meets the properties of Lemma 3.1.
--
--   **Formalization Note.** The statement is made for every feasible schedule with the property of Lemma 3.1, optimal or not; for an optimal $S$ it gives the page's claim. The page's proof shows exactly the per-job inequality ("it suffices to show that the completion time of each job in the new schedule is less than or equal to its completion time in the optimal schedule"). The reverse per-job inequality, which the page derives "from optimality", holds only for jobs of positive weight and is not stated.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 16, Lemma 3.2 and its proof

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Lemma 3.2, p. 16: for a feasible schedule `S` sequenced as in Lemma 3.1, its slot assignment
is feasible, and the schedule rebuilt from it is feasible, again sequenced as in Lemma 3.1, and
completes every job no later than `S` (so it is optimal whenever `S` is, as `w ≥ 0`). -/
theorem lemma_3_2 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (S : Sched m n) (hS : SFeasible p r S) (hseq : SlotSequenced p w r S) :
    SlotFeasible r (slotOf r S) ∧ SFeasible p r (schedOf p w r (slotOf r S)) ∧
      SlotSequenced p w r (schedOf p w r (slotOf r S)) ∧
      ∀ j, Cslot p w r (slotOf r S) j ≤ compl p S j := by sorry

end SkutellaCQP.RelDates
