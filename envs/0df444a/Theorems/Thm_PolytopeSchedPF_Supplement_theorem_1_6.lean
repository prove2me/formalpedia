-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_1_6
-- name    : PolytopeSchedPF.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:13.556385+00:00
-- url     : https://prove2.me/theorems/1aa87d26-0eb1-45f0-9ac0-cb7de529dd46
-- title:
--   Theorem 1.6 — Proportional Fairness is $4$-competitive for weighted completion time on every rate polytope, with arbitrary release dates
-- statement:
--   Let $P=\{y\in\mathbb R^n_{\ge0}: By\le\mathbf 1\}$ be any rate polytope ($B\ge0$ without zero column; no support submodularity is assumed), $w\in\mathbb R^n_{>0}$ weights, $p\in\mathbb R^n_{\ge0}$ processing requirements and $r\in\mathbb R^n_{\ge0}$ release dates. Then every Proportional Fairness schedule $y^{\mathrm{pf}}$ and every feasible schedule $y'$ satisfy
--
--   $$\sum_jw_jC_j(y^{\mathrm{pf}})\le4\sum_jw_jC_j(y').$$
--
--   This improves the previous bounds $27$ and $128$ for PF on general polytope scheduling.
--
--   Differences from the source:
--   - encoding: ALG ≤ c · OPT, OPT the infimum over feasible schedules → ALG ≤ c · (objective of y′) for every feasible speed-1 schedule y′; reason: base reading R2: equivalent to the bound on the infimum
--   - encoding: the PF schedule → every schedule satisfying the base predicate IsPFSchedule; reason: base reading R4; existence of a PF schedule is the published PolytopeSchedPF.pf_schedule_exists
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 1.6, p.4 (PDF p.6); restated and proved §7.2, pp.44–46 (PDF pp.46–48)

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 1.6** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, p.4; restated and proved
§7.2, p.44). Proportional Fairness is 4-competitive for minimizing weighted completion time in PSP
with arbitrary release dates.

For every rate polytope `P` (no support submodularity assumed; any `n`, `D`), weights `w > 0`,
processing requirements `p ≥ 0` and release dates `r ≥ 0`, every PF schedule has weighted completion
time at most `4` times that of every feasible schedule.

**Formalization Note** Reading R2: `PF ≤ 4 · OPT` is stated against every feasible schedule, which is
equivalent to the bound on the infimum. Reading R4: PF is the predicate `IsPFSchedule`; its existence
is the published `PolytopeSchedPF.pf_schedule_exists`. -/
theorem theorem_1_6 {n D : ℕ} (P : RatePolytope n D) (w p r : Fin n → ℝ)
    (hw : ∀ j, 0 < w j) (hp : ∀ j, 0 ≤ p j) (hr : ∀ j, 0 ≤ r j) :
    ∀ y, IsPFSchedule P w p r y → ∀ y', IsFeasible P p r y' →
      weightedCompletion w p r y ≤ 4 * weightedCompletion w p r y' := by sorry

end Supplement

end PolytopeSchedPF
