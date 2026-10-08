-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_lemma_3_5
-- name    : SkutellaCQP.RelDates.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:38.86411+00:00
-- url     : https://prove2.me/theorems/c6957db4-0dc7-4e41-bc7a-e7559c8d35e9
-- title:
--   Lemma 3.5, p. 20 — randomized rounding of (CQP) gives E[C_j] ≤ 2 · (19) for every job
-- statement:
--   Let $a$ be a feasible solution to (CQP) and let $\mu$ be a randomized rounding of $a$ with pairwise independent choices for the jobs. Then for every job $j$ the expected completion time of $j$ in the schedule built from the rounded slot assignment is at most twice the value (19) of $j$ in $a$, with $s_{i_k} = \rho_{i_k}$:
--   $$E[C_j] \;\le\; 2\sum_{i,k} a_{i_kj}\Big(\rho_{i_k} + \frac{1 + a_{i_kj}}{2}\,p_{ij} + \sum_{j' \prec_i j} a_{i_kj'}p_{ij'}\Big).$$
--
--   Summing over $j$ with weights $w_j$ gives the bound $2\,Z_{CQP}(a)$ on the expected value of the rounded schedule; this is the core of Theorem 3.4.
--
--   **Formalization Note.** $C_j$ is the completion time (17) of the schedule built from the rounded slot assignment; the rounding is a probability weight on slot assignments with the prescribed marginals and pairwise products.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 20, Lemma 3.5

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Lemma 3.5, p. 20: randomized rounding of a feasible solution of (CQP) gives every job an
expected completion time at most twice its value (19) (with `s = ρ`). -/
theorem lemma_3_5 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (ha : CQPFeasible p r a)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : IsPairwiseRounding a μ) :
    ∀ j, E μ (fun τ => Cslot p w r τ j) ≤ 2 * Cbar p w r a j := by sorry

end SkutellaCQP.RelDates
