-- Prove2me | Theorems.Thm_PolytopeSchedPF_display_13
-- name    : PolytopeSchedPF.display_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:44.523101+00:00
-- url     : https://prove2.me/theorems/e3527f00-f1d5-4479-8246-59ac7394ac93
-- title:
--   Display (13) — $\mathrm{OPT}(p)=\min_\pi\mathrm{OPT}_\pi(p)$
-- statement:
--   Let $w>0$ and $p\in\mathbb R^n_{\ge0}$, all jobs released at time $0$. Every feasible schedule for $p$ completes the jobs in some order $\pi$ (sort by completion time, breaking ties arbitrarily), and hence
--   $$
--   \mathrm{OPT}(p)=\min_{\pi\in S_n}\mathrm{OPT}_\pi(p).
--   $$
--   The display reduces the optimal schedule to a choice of completion order, which is how §5 bounds $\mathrm{OPT}$ by linear functions of $p$.
--
--   Differences from the source:
--   - encoding: OPT_π(p) with inf ∅ := ∞ → optOrder, an EReal-valued infimum (empty infimum ⊤); opt0 is cast to EReal for the equality; reason: the paper's ∞ is representable only in an extended type
--   - encoding: min over π ∈ S_n → the infimum over the finite type of permutations together with an order attaining it; reason: a minimum over a finite nonempty set is an attained infimum
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §5.1, p.25 (PDF p.27), display (13)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

/-- **Display (13)** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §5.1, p.25). Every feasible schedule completes the jobs in the order
obtained by sorting them by completion time, breaking ties arbitrarily, and hence
`OPT(p) = min_{π∈S_n} OPT_π(p)`.

**Formalization Note** Release dates are `0` (§5). `OPT_π` is `optOrder`, valued in `EReal` with
`inf ∅ = ∞`; the equality is stated after casting `opt0` to `EReal`, with the minimum written as an
infimum over the finite set of orders together with the existence of an order attaining it. -/
theorem display_13 {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    (∀ y, IsFeasible P p 0 y → ∃ π : Equiv.Perm (Fin n), CompletesInOrder p 0 y π) ∧
    ((opt0 P w p : ℝ) : EReal) = (⨅ π : Equiv.Perm (Fin n), optOrder P w p π) ∧
    ∃ π : Equiv.Perm (Fin n), ((opt0 P w p : ℝ) : EReal) = optOrder P w p π := by sorry

end PolytopeSchedPF
