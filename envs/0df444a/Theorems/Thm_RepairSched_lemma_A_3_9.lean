-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_9
-- name    : RepairSched.lemma_A_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:48.47778+00:00
-- url     : https://prove2.me/theorems/6304f8b8-cced-4460-861b-72b7384b2249
-- title:
--   Lemma A.3.9, OA p.16 — $\max g_\gamma$ is a bijection $[0,\gamma^{NER})\to[0,b_j\mu_j/\lambda_j)$
-- statement:
--   Let $\gamma^{NER}$ be the value of Lemma A.3.8. On $[0,\gamma^{NER})$ the maximum $\max_{w\ge0}g_\gamma(w)$ exists and is continuous and strictly increasing in $\gamma$, and
--   $$\gamma\mapsto\max_{w\ge0}g_\gamma(w)$$
--   is a bijection from $[0,\gamma^{NER})$ onto $[0,b_j\mu_j/\lambda_j)$.
--
--   This gives the unique $\gamma$ with $\max g_\gamma=c_k\mu_k$ in Lemma 2 Part ii.
--
--   **Formalization Note** $\gamma^{NER}$ is characterized by its property from Lemma A.3.8, as a hypothesis.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.9, OA p.16

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol
import Definitions.Def_RepairSched_Model_backorderRatio

open Set

namespace RepairSched

/-- **Lemma A.3.9: the maximum of `g_γ` as a function of `γ`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.9, OA p.16 (PDF p.56).

Let `γ_NER` be the value of Lemma A.3.8 and let `G γ` solve (A.2) for each `γ`. On `[0, γ_NER)` the
maximum `max_{w∈ℝ₊} G γ w` exists and is continuous and strictly increasing in `γ`, and it is a
bijection from `[0, γ_NER)` onto `[0, bjμj/λj)`.

**Formalization Note.** `γ_NER` is characterized by its defining property from Lemma A.3.8 as a
hypothesis, not chosen. The function `m` is any function giving the maximum on `[0, γ_NER)`. -/
theorem lemma_A_3_9 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (γN : ℝ) (gN : ℝ → ℝ) (hγN : 0 < γN) (hgN : M.IsIVPSol S γN gN)
    (hgNr : ∀ w, 0 ≤ w → 0 ≤ gN w ∧ gN w < M.backorderRatio)
    (G : ℝ → ℝ → ℝ) (hG : ∀ γ, M.IsIVPSol S γ (G γ)) :
    (∀ γ ∈ Ico 0 γN, ∃ m, IsGreatest (G γ '' Ici 0) m) ∧
      ∀ m : ℝ → ℝ, (∀ γ ∈ Ico 0 γN, IsGreatest (G γ '' Ici 0) (m γ)) →
        ContinuousOn m (Ico 0 γN) ∧ StrictMonoOn m (Ico 0 γN) ∧
          BijOn m (Ico 0 γN) (Ico 0 M.backorderRatio) := by sorry

end RepairSched
