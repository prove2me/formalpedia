-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_1
-- name    : RepairSched.lemma_A_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:37.588766+00:00
-- url     : https://prove2.me/theorems/53867f58-339a-4fd1-8ecc-82f4dd3a7957
-- title:
--   Lemma A.3.1, OA p.5 — existence and uniqueness of the IVP (A.2) on $\mathbb R_+$
-- statement:
--   For every $\gamma\in\mathbb R$, the initial value problem
--   $$g'(w)=\frac2\Sigma\Big(\gamma-\theta g(w)-\min_i\{b_i\mu_i-\lambda_ig(w)\}\big(w-\sum_iS_i/\mu_i\big)^+\Big),\qquad g(0)=0,$$
--   has a unique solution on $\mathbb R_+$, and it is continuously differentiable.
--
--   This solution is the candidate for $f'$ in the Bellman system.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.1, OA p.5

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol

open Set

namespace RepairSched

/-- **Lemma A.3.1: global existence and uniqueness for the IVP (A.2).**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.1, OA p.5 (PDF p.45).

For every `γ ∈ ℝ` the initial value problem (A.2) has a solution on `ℝ₊`, it is `C¹` on `ℝ₊`, and
any two solutions agree on `ℝ₊`. -/
theorem lemma_A_3_1 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (γ : ℝ) :
    (∃ g, M.IsIVPSol S γ g ∧ ContDiffOn ℝ 1 g (Ici 0)) ∧
      ∀ g₁ g₂, M.IsIVPSol S γ g₁ → M.IsIVPSol S γ g₂ → EqOn g₁ g₂ (Ici 0) := by sorry

end RepairSched
