-- Prove2me | Theorems.Thm_SkutellaCQP_Preempt_lemma_4_3
-- name    : SkutellaCQP.Preempt.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:33.772476+00:00
-- url     : https://prove2.me/theorems/6c715ebc-9928-4a8e-a433-236cfb959a01
-- title:
--   Lemma 4.3, p. 23 — randomized rounding of a feasible (ā, Z) of (CQP′_p) gives a nonpreemptive schedule of expected value ≤ 3Z, ≤ 2Z without release dates
-- statement:
--   Consider an instance of $R\mid r_{ij}\mid\sum w_jC_j$ ($w_j\ge0$, $p_{ij}>0$, $r_{ij}\ge0$). Let $(\bar a,Z)$ be a feasible solution of $(CQP'_p)$, and let Algorithm RANDOMIZED ROUNDING assign each job $j$ to the time slot $i_k$ with probability $\bar a_{i_kj}$, pairwise independently for the jobs, and then build the schedule (15)–(17) of the resulting slot assignment: the jobs of each slot are sequenced by Smith's order $\prec_i$, starting at $s_{i_1}=\rho_{i_1}$, $s_{i_{k+1}}=\max\{\rho_{i_{k+1}},s_{i_k}+\sum_{j\in i_k}p_{ij}\}$. Then:
--   1. every slot assignment drawn with positive probability is feasible, and its schedule is a feasible **nonpreemptive** schedule whose value is $\sum_j w_jC_j$ with $C_j$ given by (17);
--   2. the expected value of the schedule satisfies
--   $$
--   \mathbb E\Bigl[\sum_j w_jC_j\Bigr]\ \le\ 3\cdot Z;
--   $$
--   3. if all release dates are $0$, then $\mathbb E\bigl[\sum_j w_jC_j\bigr]\le 2\cdot Z$.
--
--   Combined with the relaxation property of $(CQP'_p)$ this compares nonpreemptive schedules with preemptive ones (Corollary 4.6).
--
--   **Formalization Note** "Algorithm RANDOMIZED ROUNDING" is any probability weight on slot assignments with marginals $\bar a$ and pairwise products (pairwise independence). Item 1 makes "computes a nonpreemptive schedule" explicit. $Z_{CQP'_p}(\bar a)$ of the page is the least $Z$ with $(\bar a,Z)$ feasible; the statement for every feasible $Z$ is equivalent. $(CQP'_p)$ includes constraint (18), $\bar a_{i_kj}=0$ if $\rho_{i_k}<r_{ij}$, which the p. 22 display omits; without it item 1 fails. "In the absence of nontrivial release dates" is read as $r_{ij}=0$ for all $i,j$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 23, Lemma 4.3

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

namespace SkutellaCQP.Preempt

theorem lemma_4_3 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (Z : ℝ) (ha : CQPpFeasible p w r a Z)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : SkutellaCQP.RelDates.IsPairwiseRounding a μ) :
    (∀ τ, μ τ ≠ 0 → SkutellaCQP.RelDates.SlotFeasible r τ ∧ PFeasible p r (toPSched p w r τ) ∧
        Nonpreemptive (toPSched p w r τ) ∧ pval w (toPSched p w r τ) = roundVal p w r τ) ∧
      SkutellaCQP.RelDates.E μ (roundVal p w r) ≤ 3 * Z ∧
      ((∀ i j, r i j = 0) → SkutellaCQP.RelDates.E μ (roundVal p w r) ≤ 2 * Z) := by sorry

end SkutellaCQP.Preempt
