-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_samplePath_submodular
-- name    : SubstOverbooking.Structure.samplePath_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:44.205041+00:00
-- url     : https://prove2.me/theorems/2110a85c-fc03-4bf2-80b6-ad25eb7f9224
-- title:
--   Proof of Theorem 2, p. 88 — sample-path submodularity: V₀((z₁+k₁, z₂+k₂)) − V₀((z₁, z₂+k₂)) ⩽ V₀((z₁+k₁, z₂)) − V₀((z₁, z₂))
-- statement:
--   Fix $a_{ij}$ and capacities $c_j \ge 0$ ($j = 1, \dots, m$). For every $z \in \mathbb R^n_{\ge 0}$, distinct classes $i \ne j$ and $k_1, k_2 \ge 0$,
--
--   $$V_0(z + k_1 e_i + k_2 e_j, c) - V_0(z + k_2 e_j, c) \le V_0(z + k_1 e_i, c) - V_0(z, c).$$
--
--   This is the pointwise inequality which, after taking expectations, gives the submodularity inequality (7) of $G$.
--
--   **Formalization Note.** The paper states this for $n = 2$ at integer realizations, and prints $V_0((z_1 + k + 1, z_2))$ for $V_0((z_1 + k_1, z_2))$ (a typo); it is stated here with $k_1$, for real nonnegative points and general $n$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 88, proof of Theorem 2, last display

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

theorem samplePath_submodular {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (hc : ∀ j, j ≠ 0 → 0 ≤ c j) (z : Fin n → ℝ) (hz : ∀ k, 0 ≤ z k) (i j : Fin n) (hij : i ≠ j)
    (k₁ k₂ : ℝ) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) :
    V0 a c (z + Pi.single i k₁ + Pi.single j k₂) - V0 a c (z + Pi.single j k₂) ≤
      V0 a c (z + Pi.single i k₁) - V0 a c z := by sorry

end SubstOverbooking.Structure
