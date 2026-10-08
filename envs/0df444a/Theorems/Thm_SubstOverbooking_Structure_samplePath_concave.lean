-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_samplePath_concave
-- name    : SubstOverbooking.Structure.samplePath_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:13.838974+00:00
-- url     : https://prove2.me/theorems/fc7c0f66-42f4-4dcd-bbe5-2738f46d002c
-- title:
--   Proof of Theorem 2, p. 88 — sample-path concavity: V₀((k₁+k₂, l)) − V₀((k₁, l)) ⩾ V₀((k₁+k₂+k₃, l)) − V₀((k₁+k₃, l))
-- statement:
--   Fix $a_{ij}$ and capacities $c_j \ge 0$ ($j = 1, \dots, m$). For every $z \in \mathbb R^n_{\ge 0}$, every class $i$ and all $k_2, k_3 \ge 0$,
--
--   $$V_0(z + (k_2 + k_3) e_i, c) - V_0(z + k_3 e_i, c) \le V_0(z + k_2 e_i, c) - V_0(z, c).$$
--
--   The increments of $V_0$ along one coordinate are nonincreasing. This is the pointwise inequality which, after taking expectations, gives the componentwise concavity (6) of $G$.
--
--   **Formalization Note.** The paper uses this at integer realizations $k_1, k_2, k_3, l$ for $n = 2$; it is stated here for real nonnegative points and general $n$ (with $z$ playing the role of $(k_1, l)$), which contains the paper's case.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 88, proof of Theorem 2, display before 'Taking expectations'

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

theorem samplePath_concave {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (z : Fin n → ℝ) (hz : ∀ k, 0 ≤ z k) (i : Fin n)
    (k₂ k₃ : ℝ) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) :
    V0 a c (z + Pi.single i (k₂ + k₃)) - V0 a c (z + Pi.single i k₃) ≤
      V0 a c (z + Pi.single i k₂) - V0 a c z := by sorry

end SubstOverbooking.Structure
