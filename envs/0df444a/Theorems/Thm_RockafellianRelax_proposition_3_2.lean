-- Prove2me | Theorems.Thm_RockafellianRelax_proposition_3_2
-- name    : RockafellianRelax.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:06.09369+00:00
-- url     : https://prove2.me/theorems/2924a156-6f3d-4aae-a7ac-22e5776a377d
-- title:
--   Proposition 3.2 — exactness from conjugacy: $f$ is exact iff $\mathcal V(0) = -\mathcal V^*(\bar y)$
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi : \mathbb R^n \to \overline{\mathbb R}$, with min-value function $\mathcal V(u) = \inf_x f(u,x)$, and let $\bar y \in \mathbb R^m$. Then $f$ is exact, supported by $\bar y$, if and only if
--
--   $$
--   \mathcal V(0) = -\mathcal V^*(\bar y).
--   $$
--
--   Exactness is therefore tightness of the Rockafellian relaxation (3.2).
--
--   Differences from the source:
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.2, p.7

import Mathlib
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_conj

namespace RockafellianRelax

/-- **Proposition 3.2 (exactness from conjugacy).** Royset, Chen & Eckstrand, arXiv:2204.04762v4,
Proposition 3.2, p.7: "Let f : ℝᵐ × ℝⁿ → R̄ be a Rockafellian for (3.1). Then f is exact, supported
by ȳ ∈ ℝᵐ, if and only if 𝒱(0) = −𝒱*(ȳ)."

**Formalization Note.** `𝒱 = minValue f`, `𝒱* = conj 𝒱`, values in `EReal`. -/
theorem proposition_3_2 {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ) :
    IsExact f φ ybar ↔ minValue f 0 = -(conj (minValue f) ybar) := by sorry

end RockafellianRelax
