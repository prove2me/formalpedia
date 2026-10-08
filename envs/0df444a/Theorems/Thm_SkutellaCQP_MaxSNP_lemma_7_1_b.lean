-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_lemma_7_1_b
-- name    : SkutellaCQP.MaxSNP.lemma_7_1_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:23.594154+00:00
-- url     : https://prove2.me/theorems/15cb5f83-2e29-4d8e-ab59-9be5ca7e51f9
-- title:
--   Lemma 7.1 b), p. 33 — OPT_SCH(R(I)) = 4n + 4m − OPT_SAT(I)
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses, and let $R(I)$ be the scheduling instance constructed from it. Then $R(I)$ has an optimal schedule, and the optimal values of $R(I)$ and of $I$ are related by
--   $$
--   \mathrm{OPT}_{\mathrm{SCH}}(R(I))=4n+4m-\mathrm{OPT}_{\mathrm{SAT}}(I),
--   $$
--   where $\mathrm{OPT}_{\mathrm{SCH}}(R(I))$ is the minimum total completion time of a feasible schedule and $\mathrm{OPT}_{\mathrm{SAT}}(I)$ is the maximum number of clauses satisfied by a truth assignment.
--
--   Together with part a) this identifies the scheduling optimum with the satisfiability optimum up to the affine map $k\mapsto 4n+4m-k$.
--
--   **Formalization Note** $\mathrm{OPT}_{\mathrm{SCH}}$ is not a primitive: the statement asserts a feasible schedule $S_0$ with $\mathrm{VAL}(S_0)=4n+4m-\mathrm{OPT}_{\mathrm{SAT}}(I)$ and $\mathrm{VAL}(S_0)\le\mathrm{VAL}(S)$ for every feasible $S$. The existence of an optimal schedule is part of the page's claim (it speaks of "the values of optimal solutions").
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 33, Lemma 7.1 b)

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Lemma 7.1 b) (p. 33). `R(I)` has an optimal schedule, and its value is
`OPT_SCH(R(I)) = 4n + 4m − OPT_SAT(I)`. -/
theorem lemma_7_1_b {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    ∃ S₀ : Sched n m, Feasible I S₀ ∧ VAL S₀ = (4 * n + 4 * m : ℝ) - optSat I ∧
      ∀ S, Feasible I S → VAL S₀ ≤ VAL S := by sorry

end SkutellaCQP.MaxSNP
