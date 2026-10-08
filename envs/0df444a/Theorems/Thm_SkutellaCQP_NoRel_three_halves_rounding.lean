-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_three_halves_rounding
-- name    : SkutellaCQP.NoRel.three_halves_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:04.49698+00:00
-- url     : https://prove2.me/theorems/bc6d28fe-5503-4a38-a833-73ac8e020ee0
-- title:
--   Lemma 2.8 and Corollary 2.9, pp. 13–14 — (CQP′) contains every schedule, and rounding any feasible (ā, Z) has expected value ≤ 3/2 · Z
-- statement:
--   Consider an instance of $R\,|\,|\sum w_jC_j$ with processing times $p_{ij}>0$ and weights $w_j\ge 0$, and the convex relaxation (CQP′):
--   $$
--   \sum_i a_{ij}=1\ \ \forall j,\qquad a\ge 0,\qquad Z\ge\tfrac12c^Ta+\tfrac12a^T(D+\operatorname{diag}(c))a\ \ (12),\qquad Z\ge c^Ta\ \ (13).
--   $$
--   Then:
--
--   1. **(CQP′) is a relaxation.** For every assignment $\sigma$ of jobs to machines (each machine sequenced by Smith's order), its $0/1$ vector $a^\sigma$ together with $Z=\sum_jw_jC_j(\sigma)$ is feasible for (CQP′). Hence $Z^*_{CQP'}\le Z^*$.
--   2. **Lemma 2.8.** For every feasible $(\bar a,Z)$ of (CQP′), Algorithm RANDOMIZED ROUNDING (each job $j$ to machine $i$ with probability $\bar a_{ij}$, choices pairwise independent) produces a schedule with
--   $$
--   \mathbb E\Bigl[\sum_jw_jC_j\Bigr]\le\tfrac32\cdot Z .
--   $$
--
--   Together the two parts say that the optimal schedule value is within a factor $3/2$ of the optimum of (CQP′) (Corollary 2.9), and that rounding a (near-)optimal solution of (CQP′) yields a randomized $3/2$-approximation for $R\,|\,|\sum w_jC_j$.
--
--   **Formalization Note** The first conjunct is what makes $Z$ a lower bound on the optimum; without it the bound of the second would be against an arbitrary number. Polynomial-time solvability of (CQP′) within additive error and derandomization are not formalized. The rounding is any probability weight on assignments with the prescribed one- and two-job marginals (pairwise independence).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), pp. 13–14, (CQP′), Lemma 2.8 and Corollary 2.9

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Goal: Corollary 2.9 (relaxation half) and Lemma 2.8 (pp. 13–14).
(1) Every assignment `σ`, with `Z` its value `∑_j w_j C_j`, is feasible for (CQP′), so the optimum of
(CQP′) is at most the optimal schedule value.
(2) For any feasible `(a, Z)` of (CQP′), randomized rounding with pairwise independent choices yields
a schedule of expected value at most `3/2 · Z`. -/
theorem three_halves_rounding {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    (∀ σ : Fin n → Fin m, CQP'Feasible p w (ind σ) (val p w σ)) ∧
    ∀ (a : Fin m → Fin n → ℝ) (Z : ℝ), CQP'Feasible p w a Z →
      ∀ μ : (Fin n → Fin m) → ℝ, IsPairwiseRounding a μ → E μ (val p w) ≤ (3 / 2) * Z := by sorry

end SkutellaCQP.NoRel
