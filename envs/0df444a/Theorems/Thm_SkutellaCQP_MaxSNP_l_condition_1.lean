-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_l_condition_1
-- name    : SkutellaCQP.MaxSNP.l_condition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:24.22604+00:00
-- url     : https://prove2.me/theorems/659018f2-ca7b-4b35-957c-3f8f9837a14b
-- title:
--   §7, proof of Theorem 7.2, p. 33 — first L-reduction condition: OPT_SCH(R(I)) ≤ 12m + 4m ≤ 32 OPT_SAT(I)
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses, let $R(I)$ be the scheduling instance constructed from it, and let $S_0$ be an optimal schedule of $R(I)$, so $\mathrm{VAL}(S_0)=\mathrm{OPT}_{\mathrm{SCH}}(R(I))$. Then
--   $$
--   \mathrm{OPT}_{\mathrm{SCH}}(R(I))\ \le\ 12m+4m\ \le\ 32\,\mathrm{OPT}_{\mathrm{SAT}}(I).
--   $$
--
--   This is the first condition of an L-reduction (Papadimitriou–Yannakakis 1991) with constant $\alpha=32$: the optimum of the target instance is bounded by a constant times the optimum of the source instance.
--
--   **Formalization Note** "$S_0$ optimal" is the pair of hypotheses: $S_0$ is feasible, and $\mathrm{VAL}(S_0)\le\mathrm{VAL}(S)$ for every feasible $S$. Both inequalities of the display are stated.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 33, §7, proof of Theorem 7.2, first display

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Proof of Theorem 7.2 (p. 33), first L-reduction condition: for an optimal schedule `S₀` of
`R(I)`, `OPT_SCH(R(I)) = VAL(S₀) ≤ 12m + 4m ≤ 32 · OPT_SAT(I)`. -/
theorem l_condition_1 {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S₀ : Sched n m) (hS₀ : Feasible I S₀) (hopt : ∀ S, Feasible I S → VAL S₀ ≤ VAL S) :
    VAL S₀ ≤ 12 * m + 4 * m ∧ (12 * m + 4 * m : ℝ) ≤ 32 * optSat I := by sorry

end SkutellaCQP.MaxSNP
