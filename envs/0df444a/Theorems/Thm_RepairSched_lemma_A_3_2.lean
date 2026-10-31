-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_2
-- name    : RepairSched.lemma_A_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:39.109451+00:00
-- url     : https://prove2.me/theorems/90b19956-7590-41b3-b678-e5094d0bdacc
-- title:
--   Lemma A.3.2, OA p.6 — $g_\gamma(w)$ is continuous and strictly increasing in $\gamma$
-- statement:
--   Let $g_\gamma$ denote the solution of (A.2) for $\gamma$. Then
--
--   1. for every fixed $w\ge0$, $\gamma\mapsto g_\gamma(w)$ is continuous on $\mathbb R$;
--   2. for every fixed $w>0$, $\gamma\mapsto g_\gamma(w)$ is strictly increasing on $\mathbb R$.
--
--   This monotonicity is what allows $\gamma$ to be chosen so that the maximum of $g_\gamma$ hits $c_k\mu_k$.
--
--   **Formalization Note** The family is any family of solutions, one for each $\gamma$.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.2, OA p.6

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol

namespace RepairSched

/-- **Lemma A.3.2: dependence of `g_γ` on `γ`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.2, OA p.6 (PDF p.46).

Let `G γ` solve (A.2) for each `γ ∈ ℝ`. For every fixed `w ≥ 0`, `γ ↦ G γ w` is continuous on `ℝ`,
and for every fixed `w > 0` it is strictly increasing on `ℝ`. -/
theorem lemma_A_3_2 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (G : ℝ → ℝ → ℝ) (hG : ∀ γ, M.IsIVPSol S γ (G γ)) :
    (∀ w, 0 ≤ w → Continuous fun γ => G γ w) ∧
      ∀ w, 0 < w → StrictMono fun γ => G γ w := by sorry

end RepairSched
