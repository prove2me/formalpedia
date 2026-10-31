-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_6
-- name    : RepairSched.lemma_A_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:42.055715+00:00
-- url     : https://prove2.me/theorems/2dcb1fb8-e963-4c51-9baa-a001f4c636de
-- title:
--   Lemma A.3.6, OA p.10 — the shape of $g_\gamma$
-- statement:
--   Write $r=b_j\mu_j/\lambda_j$ and let $g_\gamma$ solve (A.2).
--
--   1. If $\sup_{w\ge0}g_\gamma(w)\ge r$, then $g_\gamma'>0$ on $\mathbb R_+$, so $g_\gamma$ is strictly increasing and $\min g_\gamma=0$.
--   2. Suppose that $\sup_{w\ge0}g_\gamma(w)<r$. Then $g_\gamma(w)\to-\infty$ as $w\to\infty$ and $g_\gamma$ attains its maximum. If moreover $\gamma>0$:
--      - the maximum points exceed $\sum_iS_i/\mu_i$ and $g_\gamma'$ vanishes there;
--      - $g_\gamma$ is strictly increasing until the first maximum point;
--      - the maximum point is unique, and after it $g_\gamma'<0$, so $g_\gamma$ is strictly decreasing;
--      - the maximum point is strictly increasing in $\gamma$.
--
--   This lemma supplies the barrier level $B$ as the maximum point of $g_\gamma$.
--
--   **Formalization Note** The supremum is taken in the extended reals.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.6, OA p.10

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol
import Definitions.Def_RepairSched_Model_backorderRatio
import Definitions.Def_RepairSched_Model_invWork
import Definitions.Def_RepairSched_supOn

open Set Filter

namespace RepairSched

/-- **Lemma A.3.6: the shape of `g_γ`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.6, OA p.10 (PDF p.50).

Write `r = bjμj/λj` and let `g` solve (A.2) for `γ`.
1. If `sup g ≥ r`, then `g′ > 0` on `ℝ₊`, so `g` is strictly increasing and `min g = 0`.
2. Suppose that `sup g < r`.
 i. `g(w) → −∞` as `w → ∞`, and `g` attains its maximum.
 ii. If `γ > 0`, the maximum points are strictly greater than `Σᵢ Sᵢ/μᵢ` and `g′` vanishes there.
 iii. If `γ > 0`, `g` is strictly increasing until the first maximum point.
 iv. If `γ > 0`, the maximum point is unique, and after it `g′ < 0`, so `g` is strictly
 decreasing.
 v. If `γ > 0`, the unique maximum point is strictly increasing in `γ`.

**Formalization Note.** `sup` is taken in `EReal`, so it may be `+∞`. `g′(w)` is written as
`F(w, g(w), γ)`, its value by (A.2). "Maximum point" is `IsMaxOn g (Ici 0) w` with `w ≥ 0`. -/
theorem lemma_A_3_6 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i) :
    (∀ γ g, M.IsIVPSol S γ g → (M.backorderRatio : EReal) ≤ supOn g →
      (∀ w, 0 ≤ w → 0 < M.ivpField S w (g w) γ) ∧ StrictMonoOn g (Ici 0) ∧
        IsLeast (g '' Ici 0) 0) ∧
    (∀ γ g, M.IsIVPSol S γ g → supOn g < (M.backorderRatio : EReal) →
      (Tendsto g atTop atBot ∧ ∃ w, 0 ≤ w ∧ IsMaxOn g (Ici 0) w) ∧
      (0 < γ →
        (∀ w, 0 ≤ w → IsMaxOn g (Ici 0) w → M.invWork S < w ∧ M.ivpField S w (g w) γ = 0) ∧
        (∀ w₀, 0 ≤ w₀ → IsMaxOn g (Ici 0) w₀ → (∀ w, 0 ≤ w → w < w₀ → ¬ IsMaxOn g (Ici 0) w) →
          StrictMonoOn g (Icc 0 w₀)) ∧
        ∃ w₀, 0 ≤ w₀ ∧ (∀ w, 0 ≤ w → (IsMaxOn g (Ici 0) w ↔ w = w₀)) ∧
          (∀ w, w₀ < w → M.ivpField S w (g w) γ < 0) ∧ StrictAntiOn g (Ici w₀))) ∧
    (∀ γ₁ γ₂ g₁ g₂ w₁ w₂, 0 < γ₁ → γ₁ < γ₂ → M.IsIVPSol S γ₁ g₁ → M.IsIVPSol S γ₂ g₂ →
      supOn g₁ < (M.backorderRatio : EReal) → supOn g₂ < (M.backorderRatio : EReal) →
      0 ≤ w₁ → IsMaxOn g₁ (Ici 0) w₁ → 0 ≤ w₂ → IsMaxOn g₂ (Ici 0) w₂ → w₁ < w₂) := by sorry

end RepairSched
