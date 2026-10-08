-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_theorem_2_1
-- name    : SkutellaCQP.NoRel.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:25.944303+00:00
-- url     : https://prove2.me/theorems/5dadda72-6bbb-4e89-93b8-b1cb7703ab36
-- title:
--   Theorem 2.1, p. 8 — randomized rounding of a feasible (QP) solution has expected value Z_QP(ā)
-- statement:
--   Let $\bar a\in\mathbb R^{mn}$ be a feasible solution of (QP), i.e. $\sum_i\bar a_{ij}=1$ for every job $j$ and $\bar a\ge 0$. Algorithm RANDOMIZED ROUNDING assigns each job $j$ to machine $i$ with probability $\bar a_{ij}$, the choices being pairwise independent for the jobs, and sequences each machine by Smith's order. Then the expected value of the resulting schedule equals the (QP) objective:
--
--   $$
--   \mathbb E\Bigl[\sum_j w_jC_j\Bigr]=Z_{QP}(\bar a)=c^T\bar a+\tfrac12\bar a^TD\bar a .
--   $$
--
--   In particular (QP) is not a relaxation with an integrality gap: its optimum can be attained by rounding, which is Corollary 2.3. The theorem is the bridge between the value of a fractional solution and the expected value of the rounded schedule used throughout §2.
--
--   **Formalization Note** The rounding is any probability weight $\mu$ on assignments whose one-job marginals are $\bar a$ and whose two-job marginals for distinct jobs are products; full independence is not required. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 8, Theorem 2.1

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Theorem 2.1 (p. 8). For a feasible solution `a` of (QP), the expected value of the schedule
produced by randomized rounding with pairwise independent choices equals `Z_QP(a)`. -/
theorem theorem_2_1 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (ha : Feasible a)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (val p w) = ZQP p w a := by sorry

end SkutellaCQP.NoRel
