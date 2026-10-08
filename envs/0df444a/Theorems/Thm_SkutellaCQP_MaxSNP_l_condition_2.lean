-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_l_condition_2
-- name    : SkutellaCQP.MaxSNP.l_condition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:24.491215+00:00
-- url     : https://prove2.me/theorems/77d24f9d-d121-432e-89cc-9320a14c9dd0
-- title:
--   §7, proof of Theorem 7.2, p. 33 — second L-reduction condition: OPT_SAT(I) − #(SAT(S)) ≤ VAL(S) − OPT_SCH(R(I))
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses, let $R(I)$ be the scheduling instance constructed from it, and let $S_0$ be an optimal schedule of $R(I)$. For every feasible schedule $S$ of $R(I)$,
--   $$
--   \mathrm{OPT}_{\mathrm{SAT}}(I)-\#(\mathrm{SAT}(S))\ \le\ \mathrm{VAL}(S)-\mathrm{OPT}_{\mathrm{SCH}}(R(I)),
--   $$
--   where $\mathrm{OPT}_{\mathrm{SCH}}(R(I))=\mathrm{VAL}(S_0)$.
--
--   This is the second condition of an L-reduction with constant $\beta=1$: the loss of the truth assignment recovered from a schedule is at most the excess of the schedule over the optimum.
--
--   **Formalization Note** "$S_0$ optimal" is the pair of hypotheses: $S_0$ is feasible, and $\mathrm{VAL}(S_0)\le\mathrm{VAL}(S)$ for every feasible $S$. The inequality is stated over the reals.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 33, §7, proof of Theorem 7.2, second display

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Proof of Theorem 7.2 (p. 33), second L-reduction condition: for an optimal schedule `S₀` and
every feasible schedule `S` of `R(I)`, `OPT_SAT(I) − #(SAT(S)) ≤ VAL(S) − OPT_SCH(R(I))`. -/
theorem l_condition_2 {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S₀ : Sched n m) (hS₀ : Feasible I S₀) (hopt : ∀ S, Feasible I S → VAL S₀ ≤ VAL S)
    (S : Sched n m) (hS : Feasible I S) :
    (optSat I : ℝ) - satCount I (SAT S) ≤ VAL S - VAL S₀ := by sorry

end SkutellaCQP.MaxSNP
