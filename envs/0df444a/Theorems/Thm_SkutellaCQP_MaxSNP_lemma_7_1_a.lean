-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_lemma_7_1_a
-- name    : SkutellaCQP.MaxSNP.lemma_7_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:35.255984+00:00
-- url     : https://prove2.me/theorems/d07ed8b5-c1f8-4f94-9f03-f37f99db3bfb
-- title:
--   Lemma 7.1 a), p. 32 — every feasible schedule S of R(I) has #(SAT(S)) ≥ 4n + 4m − VAL(S)
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses, and let $R(I)$ be the scheduling instance constructed from it (v-jobs of length $4$ released at $0$, c-jobs of length $0$ released at $3$, a true and a false machine per variable). For every feasible schedule $S$ of $R(I)$, the truth assignment $\mathrm{SAT}(S)$ read off from the machines of the v-jobs satisfies
--   $$
--   \#(\mathrm{SAT}(S))\ \ge\ 4n+4m-\mathrm{VAL}(S),
--   $$
--   where $\#(t)$ is the number of clauses satisfied by $t$ and $\mathrm{VAL}(S)$ is the total completion time of $S$.
--
--   This is the direction of the reduction that maps schedules back to truth assignments without losing more than the schedule's excess over $4n+4m$.
--
--   **Formalization Note** The inequality is stated over the reals, so no natural-number subtraction occurs. The hypothesis that $I$ is a valid instance includes the at-most-three-occurrences condition of the page and the two conventions described in the definitions file (clauses have one to three literals, every variable occurs).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 32, Lemma 7.1 a)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Lemma 7.1 a) (p. 32). For every feasible schedule `S` of `R(I)`, the truth assignment
`SAT(S)` satisfies at least `4n + 4m − VAL(S)` clauses of `I`. -/
theorem lemma_7_1_a {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S : Sched n m) (hS : Feasible I S) :
    (4 * n + 4 * m : ℝ) - VAL S ≤ satCount I (SAT S) := by sorry

end SkutellaCQP.MaxSNP
