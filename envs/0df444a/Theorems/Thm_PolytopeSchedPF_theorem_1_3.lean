-- Prove2me | Theorems.Thm_PolytopeSchedPF_theorem_1_3
-- name    : PolytopeSchedPF.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:55.808458+00:00
-- url     : https://prove2.me/theorems/685d9ed7-e001-4ad9-b5e0-de63984f9d19
-- title:
--   Theorem 1.3 — Proportional Fairness is 2-competitive for $\sum_jw_jC_j$ on support-submodular PSP, 3-competitive with release dates
-- statement:
--   Proportional Fairness is $2$-competitive for minimizing weighted completion time in support-submodular PSP and $3$-competitive with arbitrary release dates.
--
--   Precisely: let $\mathcal P=\{y\ge0 : By\le\mathbf 1\}$ be a support-submodular rate polytope ($B\ge0$ without zero column, any $n$ and $D$), let $w\in\mathbb R^n_{>0}$, $p\in\mathbb R^n_{\ge0}$ and $r\in\mathbb R^n_{\ge0}$. Then
--
--   1. a PF schedule for $(p,r)$ exists;
--   2. every PF schedule $y^{\mathrm{pf}}$ and every feasible schedule $y$ for $(p,r)$ satisfy
--   $$
--   \sum_jw_jC_j(y^{\mathrm{pf}})\ \le\ 3\sum_jw_jC_j(y);
--   $$
--   3. if all release dates are equal, then
--   $$
--   \sum_jw_jC_j(y^{\mathrm{pf}})\ \le\ 2\sum_jw_jC_j(y).
--   $$
--
--   The factor $2$ is best possible for nonclairvoyant algorithms already on a single machine, so PF attains the optimal nonclairvoyant ratio on unrelated machines and on all support-submodular polytopes.
--
--   **Formalization Note** "$\mathrm{PF}\le c\cdot\mathrm{OPT}$" is stated against every feasible schedule, which is equivalent to the bound on the infimum $\mathrm{OPT}$. The PF schedule is the predicate `IsPFSchedule` of the definitions module.
--
--   Differences from the source:
--   - generalization: uniform release dates (all jobs released at time 0, p.29) → all r_j equal to any common value; reason: with a common r₀ every completion time, of PF and of any schedule, is r₀ plus that of the shifted instance, so the factor 2 persists; r₀ = 0 is the source's case
--   - generalization: PF(p) ≤ c · OPT(p) for the PF schedule → additionally asserts that a PF schedule exists; reason: the bounds then are not vacuous; dropping the first conjunct gives the source's claim
--   - encoding: OPT(p), the optimal objective among all feasible schedules → the bound against every feasible schedule for (p, r); reason: equivalent to the bound on the infimum, without a real sInf
--   - encoding: PF as an online algorithm, y^pf(t) = y(A(t)) → IsPFSchedule: a feasible schedule EG-optimal for its own active set at every t ≥ 0; the comparison in (CP) ranges over vectors positive on A(t); reason: Lean's log 0 = 0; the online, nonclairvoyant information model adds no condition to the inequality
--   - encoding: C_j = min{t ≥ r_j | ∫ y_j ≥ p_j}, A(t), U(t) → C_j as sInf; A(t), U(t) through accumulated processing; reason: equal to the paper's objects for every feasible schedule
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 1.3, p.2 (PDF p.4); proved §5.3, p.29 (PDF p.31): "This implies that PF(p) ≤ 3 · OPT(p). Furthermore, if all jobs are released at time 0, then the guarantee improves to PF(p) ≤ 2·OPT(p)."

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness
import Definitions.Def_PolytopeSchedPF_IsSupportSubmodular

namespace PolytopeSchedPF

/-- **Theorem 1.3** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, p.2; proved §5.3, p.29). Proportional Fairness is 2-competitive for
minimizing weighted completion time in support-submodular PSP and 3-competitive with arbitrary
release dates.

For every support-submodular instance (any `n`, `D`), weights `w > 0`, processing requirements
`p ≥ 0` and release dates `r ≥ 0`:
1. a PF schedule exists;
2. every PF schedule has weighted completion time at most `3` times that of every feasible
   schedule;
3. if all release dates are equal, at most `2` times.

**Formalization Note** Reading R2: `PF ≤ c · OPT` is stated against every feasible schedule, which
is equivalent to the bound on the infimum. Reading R4: PF is the predicate `IsPFSchedule`, and its
existence is asserted. Reading R3: "uniform release dates" is any common value of `r_j`, which
specializes to `r = 0`. -/
theorem theorem_1_3 {n D : ℕ} (P : RatePolytope n D) (hP : IsSupportSubmodular P)
    (w p r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (hp : ∀ j, 0 ≤ p j) (hr : ∀ j, 0 ≤ r j) :
    (∃ y, IsPFSchedule P w p r y) ∧
    (∀ y, IsPFSchedule P w p r y → ∀ y', IsFeasible P p r y' →
      weightedCompletion w p r y ≤ 3 * weightedCompletion w p r y') ∧
    ((∀ i j, r i = r j) → ∀ y, IsPFSchedule P w p r y → ∀ y', IsFeasible P p r y' →
      weightedCompletion w p r y ≤ 2 * weightedCompletion w p r y') := by sorry

end PolytopeSchedPF
