-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_bound_25
-- name    : SkutellaCQP.Preempt.bound_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:32.780298+00:00
-- url     : https://prove2.me/theorems/4da62b6e-513e-474c-a98f-3d37b59c7f02
-- title:
--   (25), proof of Lemma 4.2, p. 22 — (23) with ≺ᵢ replaced by the completion-time order ≺ of the schedule
-- statement:
--   Consider an instance of $R\mid r_{ij},\,pmtn\mid\sum w_jC_j$ ($w_j\ge0$, $p_{ij}>0$, $r_{ij}\ge0$) and a feasible preemptive schedule with completion times $C_j$ and slot fractions $a_{i_kj}$. Let $\prec$ be the order of the jobs by nondecreasing completion time $C_j$ in this schedule, ties broken by index. Then
--   $$
--   \sum_j w_jC_j\ \ge\ \sum_j w_j\sum_{i,k}a_{i_kj}\Bigl(\rho_{i_k}+\frac{a_{i_kj}}{2}p_{ij}+\sum_{j'\prec j}a_{i_kj'}p_{ij'}\Bigr).
--   $$
--
--   This is the modified version (25) of the bound (23), with Smith's order $\prec_i$ replaced by the completion-time order $\prec$; together with the exchange inequality it gives (23).
--
--   **Formalization Note** The page leaves ties among equal completion times open ("a total order … according to nondecreasing completion times"); they are broken by job index here. The bound holds for every tie-break.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), §4, proof of Lemma 4.2, p. 22, display (25)

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

open Finset

theorem bound_25 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (P : PSched m n) (hP : PFeasible p r P) :
    ∑ j, w j * ∑ i, ∑ k, frac p r P i k j * (SkutellaCQP.RelDates.rho r i k + frac p r P i k j / 2 * p i j +
      ∑ j' ∈ univ.filter (fun j' => cprec P j' j), frac p r P i k j' * p i j') ≤ pval w P := by sorry

end SkutellaCQP.Preempt
