-- Prove2me | Theorems.Thm_RepairSched_lemma_A_3_3
-- name    : RepairSched.lemma_A_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:46.593655+00:00
-- url     : https://prove2.me/theorems/fba1bd40-9912-4ce3-9fe0-2cb406099638
-- title:
--   Lemma A.3.3, OA p.7 — $\max g_0=0$ and $\inf g_0<0$
-- statement:
--   For the solution $g_0$ of (A.2) with $\gamma=0$,
--   $$\max_{w\in\mathbb R_+}g_0(w)=0,\qquad\inf_{w\in\mathbb R_+}g_0(w)<0.$$
--   This is the left end of the bijection of Lemma A.3.9.
--
--   Differences from the source:
--   - generalization: Σ := Σᵢ αᵢλᵢ(1+σᵢ²)/μᵢ² (p.15) → Σ > 0 a free parameter; reason: every statement depends on Σ only through Σ > 0; the source value is one such Σ
--   - encoding: SKU set {1,…,I}, indices j, k → Fin n with n ≥ 1; bjμj/λj and ckμk as minima; reason: only the values of the minima enter the statements
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma A.3.3, OA p.7

import Mathlib
import Definitions.Def_RepairSched_Model_IsIVPSol

open Set

namespace RepairSched

/-- **Lemma A.3.3: the case `γ = 0`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma A.3.3, OA p.7 (PDF p.47).

If `g` solves (A.2) for `γ = 0`, then `max_{w∈ℝ₊} g(w) = 0` and `inf_{w∈ℝ₊} g(w) < 0`.

**Formalization Note.** `max = 0` is `IsGreatest` of the image of `[0,∞)`, which asserts
attainment. `inf < 0` is the existence of a point with `g(w) < 0`, which also covers
`inf = −∞`. -/
theorem lemma_A_3_3 {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i)
    (g : ℝ → ℝ) (hg : M.IsIVPSol S 0 g) :
    IsGreatest (g '' Ici 0) 0 ∧ ∃ w, 0 ≤ w ∧ g w < 0 := by sorry

end RepairSched
