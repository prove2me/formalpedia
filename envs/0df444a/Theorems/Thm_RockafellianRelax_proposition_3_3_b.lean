-- Prove2me | Theorems.Thm_RockafellianRelax_proposition_3_3_b
-- name    : RockafellianRelax.proposition_3_3_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:36.322267+00:00
-- url     : https://prove2.me/theorems/bdf97db1-40c2-45e0-b8f1-5a0bc80dc531
-- title:
--   Proposition 3.3 (second claim) — when $\operatorname{argmin}\varphi \ne \emptyset$, (3.3) implies exactness
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi : \mathbb R^n \to \overline{\mathbb R}$ and $\bar y \in \mathbb R^m$. Suppose $\operatorname{argmin}_x\varphi(x) \ne \emptyset$ and that (3.3) holds:
--
--   $$
--   x^\star \in \operatorname*{argmin}_x \varphi(x) \implies (0, x^\star) \in \operatorname*{argmin}_{u,x}\bigl\{f(u,x) - \langle\bar y, u\rangle\bigr\}\quad\text{for every } x^\star .
--   $$
--
--   Then $f$ is exact, supported by $\bar y$.
--
--   Differences from the source:
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.3, p.7

import Mathlib
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Proposition 3.3, second claim: (3.3) gives exactness when argmin φ ≠ ∅.** Royset, Chen &
Eckstrand, arXiv:2204.04762v4, Proposition 3.3, p.7: "Suppose f : ℝᵐ×ℝⁿ → R̄ is a Rockafellian for
the problem (3.1) of minimizing φ : ℝⁿ → R̄. … When argmin_x φ(x) ≠ ∅, (3.3) conversely implies
exactness."

**Formalization Note.** (3.3) is `x⋆ ∈ argmin φ ⟹ (0, x⋆) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩` for every
`x⋆`; every `argmin` carries the domain condition of p.6. -/
theorem proposition_3_3_b {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ)
    (hne : (argmin φ).Nonempty)
    (h33 : ∀ xs : Fin n → ℝ, xs ∈ argmin φ → ((0 : Fin m → ℝ), xs) ∈ argmin (tilt f ybar)) :
    IsExact f φ ybar := by sorry

end RockafellianRelax
