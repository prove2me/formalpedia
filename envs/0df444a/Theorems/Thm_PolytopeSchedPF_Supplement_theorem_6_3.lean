-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_6_3
-- name    : PolytopeSchedPF.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:46.242506+00:00
-- url     : https://prove2.me/theorems/a04b170b-5327-4d5f-b541-f477ecf53d1e
-- title:
--   Theorem 6.3 — with a $c$-approximate certificate, PF with speed $\kappa>2c$ is $\kappa/(\kappa-2c)$-competitive for weighted flow time
-- statement:
--   Let $P$ be a rate polytope, $w\in\mathbb R^n_{>0}$, and suppose $P$ admits a $c$-approximate certificate for $w$ (Definition 6.1). Then:
--
--   1. for every $\kappa>2c$, all $p\in\mathbb R^n_{\ge0}$ and all release dates $r\in\mathbb R^n_{\ge0}$, the schedule of Proportional Fairness with speed $\kappa$ and every feasible (speed-$1$) schedule $y'$ satisfy
--
--   $$\sum_jw_j\big(C^{\mathrm{pf}}_j-r_j\big)\le\frac{\kappa}{\kappa-2c}\sum_jw_j\big(C_j(y')-r_j\big);$$
--
--   2. in particular, for every $\varepsilon>0$, PF with speed $2c+\varepsilon$ satisfies the same bound with factor $(2c+\varepsilon)/\varepsilon$, so PF is $(2c+\varepsilon)$-speed $O(c/\varepsilon)$-competitive.
--
--   This general result yields both the support-submodular guarantee (Theorem 6.6, $c=1$) and the guarantee for sparse binary polytopes and graph scheduling (Theorem 6.8, Corollary 6.12).
--
--   Differences from the source:
--   - reading: O(c/ε)-competitive → the explicit factor (2c + ε)/ε, the first part at κ = 2c + ε; reason: the paper derives the in-particular from the first sentence; (2c + ε)/ε is O(c/ε) for bounded ε
--   - encoding: PF with speed augmentation κ and its weighted flow time → a PF schedule for p/κ (rates in P), with flow time computed from completionTime (p/κ) r; reason: p.13: an s-speed feasible schedule for (p_j) is a 1-speed feasible schedule for (p_j/s), with the same completion times, and PF with speed s uses the same rule
--   - encoding: a downward-closed (rate) polytope P ⊆ ℝⁿ≥0 → a base RatePolytope {y ≥ 0 | By ≤ 1} with B ≥ 0 and no zero column; reason: base reading R1: every downward-closed polytope containing a positive multiple of each unit vector has such a description
--   - encoding: ALG ≤ c · OPT, OPT the infimum over feasible schedules → ALG ≤ c · (objective of y′) for every feasible speed-1 schedule y′; reason: base reading R2: equivalent to the bound on the infimum
--   - encoding: the PF schedule → every schedule satisfying the base predicate IsPFSchedule; reason: base reading R4; existence of a PF schedule is the published PolytopeSchedPF.pf_schedule_exists
--   - generalization: speed augmentation s ≥ 1 (Definition 3.1) and κ > 2c → every real κ > 2c, with no κ ≥ 1 and no sign condition on c; reason: with n ≥ 1 a c-approximate certificate forces c ≥ 1 (p = e_j in (i) and (iii)), so κ > 2c already gives κ > 2; the extra cases (κ < 1 or c < 1/2) occur only at n = 0, where both flow times are 0; specializes to the source on every instance it allows
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 6.3, §6, p.34 (PDF p.36); Definition 6.1, p.33 (PDF p.35); speed augmentation §3.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PolytopeSchedPF_ProportionalFairness
import Definitions.Def_PolytopeSchedPF_Supplement_weightedFlow
import Definitions.Def_PolytopeSchedPF_Supplement_ApproxCertificate

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 6.3** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §6, p.34). For any
`κ > 2c`, Proportional Fairness with speed augmentation `κ` is `κ/(κ−2c)`-competitive for
minimizing weighted flow time on every polytope that admits a `c`-approximate certificate for the job
weights. In particular, PF is `(2c + ε)`-speed `O(c/ε)`-competitive for every `ε > 0`.

Let `P` be a rate polytope, `w > 0`, and suppose `P` admits a `c`-approximate certificate for `w`.
1. For every `κ > 2c`, all `p ≥ 0`, `r ≥ 0`: every PF schedule with speed `κ` (a PF schedule for
   `p / κ`) has weighted flow time at most `κ/(κ − 2c)` times that of every feasible speed-1
   schedule for `p`.
2. For every `ε > 0`, the same holds with speed `2c + ε` and factor `(2c + ε)/ε`.

**Formalization Note** `O(c/ε)` is stated with the explicit factor `(2c + ε)/ε` of part 1. Speed `κ`
follows p.13 (`p_j / κ`, rates in `P`). Reading R2: the bound is against every feasible schedule. -/
theorem theorem_6_3 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (c : ℝ) (hcert : AdmitsApproxCertificate P w c) :
    (∀ κ : ℝ, 2 * c < κ → ∀ p r : Fin n → ℝ, (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ r j) →
      ∀ y, IsPFSchedule P w (fun j => p j / κ) r y → ∀ y', IsFeasible P p r y' →
        weightedFlow w (fun j => p j / κ) r y ≤ κ / (κ - 2 * c) * weightedFlow w p r y') ∧
    (∀ ε : ℝ, 0 < ε → ∀ p r : Fin n → ℝ, (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ r j) →
      ∀ y, IsPFSchedule P w (fun j => p j / (2 * c + ε)) r y → ∀ y', IsFeasible P p r y' →
        weightedFlow w (fun j => p j / (2 * c + ε)) r y ≤
          (2 * c + ε) / ε * weightedFlow w p r y') := by sorry

end Supplement

end PolytopeSchedPF
