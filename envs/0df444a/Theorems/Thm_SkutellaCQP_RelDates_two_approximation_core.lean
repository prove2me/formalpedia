-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_two_approximation_core
-- name    : SkutellaCQP.RelDates.two_approximation_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:43.402976+00:00
-- url     : https://prove2.me/theorems/dd605f76-2fdc-47b5-8de2-3a53f16679dc
-- title:
--   Theorem 3.4, pp. 19–20 — randomized rounding of (CQP) is a 2-approximation for R | rᵢⱼ | Σ wⱼCⱼ
-- statement:
--   Consider $R \mid r_{ij} \mid \sum w_jC_j$ with processing times $p_{ij} > 0$, weights $w_j \ge 0$ and release dates $r_{ij} \ge 0$. Then:
--
--   1. **The output is a schedule.** For every feasible assignment $\tau$ of jobs to time slots, the schedule constructed from $\tau$ (each slot sequenced by $\prec_i$, slot starts (15)–(16)) is a feasible nonpreemptive schedule, with completion times $C_j(\tau)$ given by (17).
--   2. **Rounding loses at most a factor 2 against (CQP).** For every feasible solution $a$ of (CQP) and every randomized rounding $\mu$ of $a$ with pairwise independent choices,
--   $$E_\mu\Big[\sum_j w_jC_j(\tau)\Big] \;\le\; 2\,Z_{CQP}(a).$$
--   3. **(CQP) is a relaxation.** For every feasible schedule $S$ there is a feasible solution $a$ of (CQP) with
--   $$Z_{CQP}(a) \le \sum_j w_jC_j(S).$$
--
--   Together: rounding an optimal (or any) solution $a$ of (CQP) produces a feasible schedule whose expected value is at most $2\,Z_{CQP}(a) \le 2\cdot\mathrm{OPT}$. This is Theorem 3.4 without its running-time claim, and it also gives the positive half of Corollary 3.6: the optimum of (CQP) is within a factor 2 of the optimal schedule value.
--
--   **Formalization Note.** Polynomial running time (solving (CQP)) is not formalized. The bound is stated for every feasible $a$, not only an optimal one, so no existence of an optimum of (CQP) is needed. Randomized rounding is a probability weight on slot assignments with marginals $a$ and pairwise independent choices; its support consists of feasible slot assignments because of (18).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), pp. 19–20, Theorem 3.4 and the sentence after the proof of Lemma 3.5

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- Theorem 3.4, pp. 19–20 (formal core): rounded slot assignments are feasible schedules with
completion times (17); pairwise independent randomized rounding of any feasible solution of (CQP)
has expected value at most `2 Z_CQP(a)`; and (CQP) is a relaxation of R | r_ij | ∑ w_j C_j. -/
theorem two_approximation_core {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j) :
    (∀ τ : Fin n → Fin m × Fin n, SlotFeasible r τ →
        SFeasible p r (schedOf p w r τ) ∧ ∀ j, compl p (schedOf p w r τ) j = Cslot p w r τ j) ∧
      (∀ a : Fin m → Fin n → Fin n → ℝ, CQPFeasible p r a →
        ∀ μ : (Fin n → Fin m × Fin n) → ℝ, IsPairwiseRounding a μ →
          E μ (fun τ => ∑ j, w j * Cslot p w r τ j) ≤ 2 * ZCQP p w r a) ∧
      (∀ S : Sched m n, SFeasible p r S →
        ∃ a : Fin m → Fin n → Fin n → ℝ, CQPFeasible p r a ∧ ZCQP p w r a ≤ sval p w S) := by sorry

end SkutellaCQP.RelDates
