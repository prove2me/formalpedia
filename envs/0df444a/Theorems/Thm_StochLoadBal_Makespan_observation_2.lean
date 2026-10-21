-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_observation_2
-- name    : StochLoadBal.Makespan.observation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:07.487682+00:00
-- url     : https://prove2.me/theorems/932f386a-22cc-4451-a1f7-f4d4bee0d07c
-- title:
--   Observation 2 — y is feasible for the GAP relaxation with makespan b and cost ≤ 2, p_ij ≤ 1, and an assignment with (13)–(14) exists
-- statement:
--   Let $m\ge1$, let the sizes $X_{ij}\ge0$ be measurable and integrable, let $b\ge0$, and let $y$ be a feasible solution of the LP (5)–(9) with parameter $b$. Let $p_{ij}=\beta_{\ell_i}(X'_{ij})$ and $c_{ij}=\mathbb E[X''_{ij}]$ be the data of the GAP instance $I$ built by the rounding. Then:
--
--   1. $y$ satisfies the makespan constraints of the natural GAP relaxation, $\sum_j p_{ij}\,y_{ij}\le b$ for every machine $i$;
--   2. its fractional cost is at most $2$: $\sum_{i,j} c_{ij}\,y_{ij}\le 2$;
--   3. every processing time is at most $1$: $p_{ij}\le1$;
--   4. there is an assignment $\sigma$ satisfying (13) and (14):
--   $$\sum_{i=1}^m\sum_{j\in J_i}\mathbb E[X''_{ij}]\le 2,\qquad \sum_{j\in J_i}\beta_{\ell_i}(X'_{ij})\le b+1\ \ \forall i.$$
--
--   Part 4 is what the Shmoys–Tardos rounding for the generalized assignment problem delivers on instance $I$ (cost at most the fractional cost, makespan at most $b+\max_{ij}p_{ij}\le b+1$); with Lemma 6 it gives the upper-bound half of Theorem 1.
--
--   **Formalization Note** The Shmoys–Tardos algorithm is only cited by the paper; it is represented here by the existence of an assignment with its guarantee (13)–(14), which is the only property of it the analysis uses. The constraints (11)–(12) of the GAP relaxation are (5) and the bound $p_{ij}\le 1$.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 11, Observation 2 (proof p. 12, eqs. (10)–(14))

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Observation 2 (p. 11; proof p. 12): for `b ≥ 0` and a feasible LP solution `y`,
(i) `y` is feasible for the natural LP relaxation of the GAP instance `I` with makespan `b`
and fractional cost at most `2`, and every `p_{ij} ≤ 1`; (ii) there is an assignment with
properties (13)–(14) (the Shmoys–Tardos rounding). -/
theorem observation_2 {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P)
    (b : ℝ) (hb : 0 ≤ b) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y) :
    (∀ i, ∑ j, procTime P X b y i j * y i j ≤ b) ∧
    (∑ i, ∑ j, gapCost P X i j * y i j ≤ 2) ∧
    (∀ i j, procTime P X b y i j ≤ 1) ∧
    ∃ σ : Fin n → Fin m, IsRoundingOutput P X b y σ := by sorry

end StochLoadBal.Makespan
