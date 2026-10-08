-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_theorem_2_6_a
-- name    : SkutellaCQP.NoRel.theorem_2_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:12.931818+00:00
-- url     : https://prove2.me/theorems/7e50f92e-8ee7-4091-a053-c30c97b88ca9
-- title:
--   Theorem 2.6 a), p. 12 — rounding an optimum of (CQP) gives expected value ≤ 2 × every schedule's value
-- statement:
--   Let $\bar a$ be an optimum solution of (CQP): $\bar a$ satisfies (5)–(6) and $Z_{CQP}(\bar a)\le Z_{CQP}(a)$ for every feasible $a$. Apply Algorithm RANDOMIZED ROUNDING to $\bar a$ (each job $j$ goes to machine $i$ with probability $\bar a_{ij}$, pairwise independently). Then for every assignment $\tau$
--
--   $$
--   \mathbb E\Bigl[\sum_jw_jC_j\Bigr]\le 2\cdot\sum_jw_jC_j(\tau),
--   $$
--
--   that is, the expected value is at most twice the optimum $Z^*$ of $R\,|\,|\sum w_jC_j$. This is the value guarantee of the randomized 2-approximation algorithm of part a).
--
--   **Formalization Note** The paper's statement also asserts that the algorithm runs in polynomial time; running time is not formalized. "Within a factor 2 of the optimum" is written as a bound against every assignment, so no optimal schedule is presupposed. (CQP) does have an optimum whenever $m\ge 1$ (a continuous function on a nonempty compact set), so the optimality hypothesis is satisfiable. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 12, Theorem 2.6 a)

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Theorem 2.6 a) (p. 12), without running time. If `a` is an optimum solution of (CQP), randomized
rounding with pairwise independent choices yields a schedule of expected value at most twice the
value of every schedule. -/
theorem theorem_2_6_a {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (ha : Feasible a)
    (hopt : ∀ b : Fin m → Fin n → ℝ, Feasible b → ZCQP p w a ≤ ZCQP p w b)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    ∀ σ : Fin n → Fin m, E μ (val p w) ≤ 2 * val p w σ := by sorry

end SkutellaCQP.NoRel
