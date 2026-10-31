-- Prove2me | Theorems.Thm_RepairSched_lemma_2_ii
-- name    : RepairSched.lemma_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:19.684065+00:00
-- url     : https://prove2.me/theorems/e8e445d1-995c-418d-a1eb-aaafd0b32117
-- title:
--   Lemma 2 Part ii, p.21 — the Bellman system (13) has a solution, with $(B,\gamma)$ unique
-- statement:
--   Suppose that $b_j\mu_j/\lambda_j>c_k\mu_k$ and fix $S\in\mathbb R^n_+$. There is a triple $(f,B,\gamma)$ with $f\in C^2$, $B>0$, $\gamma\ge0$ satisfying (13). For all solutions:
--
--   1. $(B,\gamma)$ is unique;
--   2. $f$ is unique up to a constant on $[0,B]$;
--   3. $B>\sum_iS_i/\mu_i$ and $\gamma>0$;
--   4. $f'$ is strictly increasing on $[0,B]$.
--
--   The triple gives the barrier level and the optimal cost of Theorem 2.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
--   - encoding: f ∈ C₂ with domain ℝ₊ → f : ℝ → ℝ, C² on ℝ, with (13) imposed for w ≥ 0; reason: a C² function on [0,∞) extends to ℝ, so no solution is lost
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 2 Part ii, p.21

import Mathlib
import Definitions.Def_RepairSched_Model_IsBellman
import Definitions.Def_RepairSched_Model_backorderRatio
import Definitions.Def_RepairSched_Model_invWork

open Set

namespace RepairSched

/-- **Lemma 2 Part ii: the Bellman system (13) has a solution.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 2 Part ii, p.21.

Suppose that `bjμj/λj > ckμk` and fix `S ∈ ℝ^I₊`. There exists `(f, B, γ)` satisfying (13). For all
solutions, `(B, γ)` is unique, `f` is unique up to a constant on `[0,B]`, `B > Σᵢ Sᵢ/μᵢ`, `γ > 0`,
and `f′` is strictly increasing on `[0,B]`. -/
theorem lemma_2_ii {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (hEm : M.emergencyRate < M.backorderRatio) :
    (∃ f B γ, M.IsBellman S f B γ) ∧
    (∀ f₁ B₁ γ₁ f₂ B₂ γ₂, M.IsBellman S f₁ B₁ γ₁ → M.IsBellman S f₂ B₂ γ₂ →
      B₁ = B₂ ∧ γ₁ = γ₂ ∧ ∃ c, ∀ w ∈ Icc 0 B₁, f₁ w = f₂ w + c) ∧
    ∀ f B γ, M.IsBellman S f B γ →
      M.invWork S < B ∧ 0 < γ ∧ StrictMonoOn (deriv f) (Icc 0 B) := by sorry

end RepairSched
