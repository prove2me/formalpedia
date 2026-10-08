-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_lemma_3_3
-- name    : SkutellaCQP.RelDates.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:39.291063+00:00
-- url     : https://prove2.me/theorems/1d8da9be-d849-4eaf-96ae-e45b70635252
-- title:
--   Lemma 3.3, p. 18 — the quadratic programming relaxation has an optimal solution with s_{i_k} = ρ_{i_k}
-- statement:
--   Consider an instance of $R \mid r_{ij} \mid \sum w_jC_j$ with $m \ge 1$ machines, processing times $p_{ij} > 0$, weights $w_j \ge 0$ and release dates $r_{ij} \ge 0$. The quadratic programming relaxation of p. 17 has assignment variables $a_{i_kj}$ subject to (14) $\sum_{i,k} a_{i_kj} = 1$, (18) $a_{i_kj} = 0$ whenever $\rho_{i_k} < r_{ij}$, and (20) $a \ge 0$; the slot starts are given by (15)–(16),
--   $$s_{i_1} = \rho_{i_1}, \qquad s_{i_{k+1}} = \max\Big\{\rho_{i_{k+1}},\ s_{i_k} + \sum_j a_{i_kj}p_{ij}\Big\},$$
--   and the objective is $\sum_j w_jC_j$ with
--   $$C_j = \sum_{i,k} a_{i_kj}\Big(s_{i_k} + \frac{1 + a_{i_kj}}{2}\,p_{ij} + \sum_{j' \prec_i j} a_{i_kj'}p_{ij'}\Big) \qquad (19).$$
--   Then this relaxation has an optimal solution $a$ (a feasible $a$ whose objective is at most that of every feasible $a'$) that satisfies $s_{i_k} = \rho_{i_k}$ for all $i$ and $k$.
--
--   As a consequence the variables $s_{i_k}$ can be replaced by the constants $\rho_{i_k}$, with (16) replaced by the capacity constraints (21) $\sum_j a_{i_kj}p_{ij} \le \rho_{i_{k+1}} - \rho_{i_k}$; this gives the convex program (CQP).
--
--   **Formalization Note.** The existence of an optimum is part of the statement, as on the page. The hypothesis $m \ge 1$ is added: with no machine and at least one job, (14) cannot be met and the relaxation has no solution. The step size printed in the page's proof, $\delta := \min\{s_{i_k} - \rho_{i_k}, a_{i_{k-1}\hat\jmath}\}$, should have its first entry divided by $p_{i\hat\jmath}$; this does not affect the statement.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 18, Lemma 3.3 and its proof, and (21)

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Lemma 3.3, p. 18: the quadratic programming relaxation ((14)–(16), (18)–(20)) has an optimal
solution with `s_{i_k} = ρ_{i_k}` for all `i` and `k`. (`0 < m`: with no machine the relaxation has
no feasible solution once there is a job.) -/
theorem lemma_3_3 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (hm : 0 < m) :
    ∃ a : Fin m → Fin n → Fin n → ℝ, QPFeasible r a ∧
      (∀ a' : Fin m → Fin n → Fin n → ℝ, QPFeasible r a' → ZQPrel p w r a ≤ ZQPrel p w r a') ∧
      ∀ i k, sStart p r a i k = rho r i k := by sorry

end SkutellaCQP.RelDates
