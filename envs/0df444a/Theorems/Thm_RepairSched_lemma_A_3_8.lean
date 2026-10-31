-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_8
-- name    : RepairSched.lemma_A_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:06.377082+00:00
-- url     : https://prove2.me/theorems/132c032c-1b71-4b39-9fde-bbaa309820c1
-- title:
--   Lemma A.3.8, OA p.15 — the value $\gamma^{NER}$
-- statement:
--   There is a unique $\gamma>0$ such that $0\le g_\gamma(w)<b_j\mu_j/\lambda_j$ for all $w\ge0$. Moreover $g_\gamma'>0$ on $\mathbb R_+$, so $g_\gamma$ is strictly increasing, and
--   $$\lim_{w\to\infty}g_\gamma(w)=\sup_{w\ge0}g_\gamma(w)=\frac{b_j\mu_j}{\lambda_j}.$$
--   This $\gamma$ is the cost of never using emergency repairs, and it bounds the range of $\gamma$ in Lemma A.3.9.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.8, OA p.15

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol
import Definitions.Def_RepairSched_Model_backorderRatio
import Definitions.Def_RepairSched_supOn

open Set Filter Topology

namespace RepairSched

/-- **Lemma A.3.8: the value `γ_NER`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.8, OA p.15 (PDF p.55).

There is a unique `γ > 0` such that `0 ≤ g_γ(w) < bjμj/λj` for all `w ≥ 0`. Moreover `g_γ′ > 0` on
`ℝ₊`, so `g_γ` is strictly increasing, `g_γ(w) → bjμj/λj` as `w → ∞`, and
`sup g_γ = bjμj/λj`. -/
theorem lemma_A_3_8 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i) :
    ∃ γ g, 0 < γ ∧ M.IsIVPSol S γ g ∧ (∀ w, 0 ≤ w → 0 ≤ g w ∧ g w < M.backorderRatio) ∧
      (∀ w, 0 ≤ w → 0 < M.ivpField S w (g w) γ) ∧ StrictMonoOn g (Ici 0) ∧
      Tendsto g atTop (𝓝 M.backorderRatio) ∧ supOn g = (M.backorderRatio : EReal) ∧
      ∀ γ' g', 0 < γ' → M.IsIVPSol S γ' g' →
        (∀ w, 0 ≤ w → 0 ≤ g' w ∧ g' w < M.backorderRatio) → γ' = γ := by sorry

end RepairSched
