-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_6_6
-- name    : PolytopeSchedPF.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:24:18.267831+00:00
-- url     : https://prove2.me/theorems/02b46b21-6b4e-4423-aece-7e577262b0eb
-- title:
--   Theorem 6.6 — on support-submodular PSP, PF with speed $\kappa>2$ is $\kappa/(\kappa-2)$-competitive for weighted flow time
-- statement:
--   Let $P$ be a support-submodular rate polytope and $w\in\mathbb R^n_{>0}$. Then:
--
--   1. for every $\kappa>2$, all $p\in\mathbb R^n_{\ge0}$ and all release dates $r\in\mathbb R^n_{\ge0}$, the schedule of Proportional Fairness with speed $\kappa$ and every feasible (speed-$1$) schedule $y'$ satisfy
--
--   $$\sum_jw_j\big(C^{\mathrm{pf}}_j-r_j\big)\le\frac{\kappa}{\kappa-2}\sum_jw_j\big(C_j(y')-r_j\big);$$
--
--   2. in particular, for every $\varepsilon>0$, PF with speed $2+\varepsilon$ satisfies the same bound with factor $(2+\varepsilon)/\varepsilon$, so PF is $(2+\varepsilon)$-speed $O(1/\varepsilon)$-competitive.
--
--   This is the paper's main flow-time result (stated in the introduction as Theorem 1.4); it covers unrelated machines and polymatroids.
--
--   Differences from the source:
--   - reading: O(1/ε)-competitive → the explicit factor (2 + ε)/ε, the first part at κ = 2 + ε; reason: the paper derives the in-particular from the first sentence; (2 + ε)/ε is O(1/ε) for bounded ε
--   - encoding: PF with speed augmentation κ and its weighted flow time → a PF schedule for p/κ (rates in P), with flow time computed from completionTime (p/κ) r; reason: p.13: an s-speed feasible schedule for (p_j) is a 1-speed feasible schedule for (p_j/s), with the same completion times, and PF with speed s uses the same rule
--   - encoding: ALG ≤ c · OPT, OPT the infimum over feasible schedules → ALG ≤ c · (objective of y′) for every feasible speed-1 schedule y′; reason: base reading R2: equivalent to the bound on the infimum
--   - encoding: the PF schedule → every schedule satisfying the base predicate IsPFSchedule; reason: base reading R4; existence of a PF schedule is the published PolytopeSchedPF.pf_schedule_exists
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 6.6, §6.1, p.36 (PDF p.38); Theorem 1.4, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness
import Definitions.Def_PolytopeSchedPF_IsSupportSubmodular
import Definitions.Def_PolytopeSchedPF_Supplement_weightedFlow

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 6.6** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §6.1, p.36; also
Theorem 1.4, p.2). For any `κ > 2`, Proportional Fairness with speed augmentation `κ` is
`κ/(κ−2)`-competitive for minimizing weighted flow time in support-submodular PSP. In particular, PF
is `(2 + ε)`-speed `O(1/ε)`-competitive for every `ε > 0`.

Let `P` be support submodular and `w > 0`.
1. For every `κ > 2`, all `p ≥ 0`, `r ≥ 0`: every PF schedule with speed `κ` (a PF schedule for
   `p / κ`) has weighted flow time at most `κ/(κ − 2)` times that of every feasible speed-1
   schedule for `p`.
2. For every `ε > 0`, the same holds with speed `2 + ε` and factor `(2 + ε)/ε`.

**Formalization Note** `O(1/ε)` is stated with the explicit factor `(2 + ε)/ε` of part 1. Speed `κ`
follows p.13 (`p_j / κ`, rates in `P`). Reading R2: the bound is against every feasible schedule. -/
theorem theorem_6_6 {n D : ℕ} (P : RatePolytope n D) (hP : IsSupportSubmodular P)
    (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    (∀ κ : ℝ, 2 < κ → ∀ p r : Fin n → ℝ, (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ r j) →
      ∀ y, IsPFSchedule P w (fun j => p j / κ) r y → ∀ y', IsFeasible P p r y' →
        weightedFlow w (fun j => p j / κ) r y ≤ κ / (κ - 2) * weightedFlow w p r y') ∧
    (∀ ε : ℝ, 0 < ε → ∀ p r : Fin n → ℝ, (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ r j) →
      ∀ y, IsPFSchedule P w (fun j => p j / (2 + ε)) r y → ∀ y', IsFeasible P p r y' →
        weightedFlow w (fun j => p j / (2 + ε)) r y ≤ (2 + ε) / ε * weightedFlow w p r y') := by sorry

end Supplement

end PolytopeSchedPF
