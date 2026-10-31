-- Prove2me | Theorems.Thm_RepairSched_lemma_1
-- name    : RepairSched.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:26.951387+00:00
-- url     : https://prove2.me/theorems/5e114c88-14f1-47ee-a816-cfec763d2b62
-- title:
--   Lemma 1, pp.20–21 — the optimal solution and value of the allocation problem (14)
-- statement:
--   Fix $w\ge0$ and a slope $y$ with $0\le y\le b_j\mu_j/\lambda_j$, and consider
--   $$z(w)=\min_{q\in\mathcal A(w)}\sum_i\Big(b_i-\frac{\lambda_i}{\mu_i}y\Big)(q_i-S_i)^+.$$
--
--   1. If $w\le\sum_iS_i/\mu_i$, then $z(w)=0$, every $q\in\mathcal A(w)$ with $q_i\le S_i$ for all $i$ attains it, and such a $q$ exists.
--   2. If $w>\sum_iS_i/\mu_i$, then for every $\kappa\in\arg\min_i\{b_i\mu_i-\lambda_iy\}$ the allocation $q_i=S_i$ $(i\ne\kappa)$, $q_\kappa=\mu_\kappa(w-\sum_{i\ne\kappa}S_i/\mu_i)$ is optimal, and
--   $$z(w)=\min_i\{b_i\mu_i-\lambda_iy\}\Big(w-\sum_iS_i/\mu_i\Big).$$
--
--   This closed form turns the Bellman equations into a first-order differential equation.
--
--   Differences from the source:
--   - generalization: f ∈ C₂ with 0 ≤ f′(w) ≤ bjμj/λj → any real y with 0 ≤ y ≤ bjμj/λj; reason: only the number f′(w) enters; take y = f′(w)
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1, pp.20–21

import Mathlib
import Definitions.Def_RepairSched_Model_allocSet
import Definitions.Def_RepairSched_Model_allocCost
import Definitions.Def_RepairSched_Model_backorderRatio
import Definitions.Def_RepairSched_Model_invWork
import Definitions.Def_RepairSched_Model_F0
import Definitions.Def_RepairSched_Model_singleBackorderAlloc

namespace RepairSched

/-- **Lemma 1: the solution of the allocation problem (14).**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1, pp.20–21 (PDF pp.20–21).

Fix `w ≥ 0` and a slope `y` with `0 ≤ y ≤ bjμj/λj`. If `w ≤ Σᵢ Sᵢ/μᵢ`, the optimal value of (14) is
`0`, any `q ∈ A(w)` with `qᵢ ≤ Sᵢ` for all `i` attains it, and such a `q` exists. If
`w > Σᵢ Sᵢ/μᵢ`, then for every `κ ∈ arg minᵢ {bᵢμᵢ − λᵢy}` the allocation of Lemma 1 Part ii lies
in `A(w)` and is optimal, with optimal value `minᵢ {bᵢμᵢ − λᵢy} (w − Σᵢ Sᵢ/μᵢ)`.

**Formalization Note.** Only the number `y = f′(w)` enters the lemma, so it is stated for every
real `y` in the range. The optimal value `z(w)` is the least element of the image of `A(w)`. -/
theorem lemma_1 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (w : ℝ) (hw : 0 ≤ w) (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ M.backorderRatio) :
    (w ≤ M.invWork S →
      IsLeast (M.allocCost S y '' M.allocSet w) 0 ∧
      (∀ q ∈ M.allocSet w, (∀ i, q i ≤ S i) → M.allocCost S y q = 0) ∧
      ∃ q ∈ M.allocSet w, ∀ i, q i ≤ S i) ∧
    (M.invWork S < w →
      ∀ κ, (∀ i, M.b κ * M.mu κ - M.lam κ * y ≤ M.b i * M.mu i - M.lam i * y) →
        M.singleBackorderAlloc S κ w ∈ M.allocSet w ∧
        M.allocCost S y (M.singleBackorderAlloc S κ w) = M.F0 y * (w - M.invWork S) ∧
        IsLeast (M.allocCost S y '' M.allocSet w) (M.F0 y * (w - M.invWork S))) := by sorry

end RepairSched
