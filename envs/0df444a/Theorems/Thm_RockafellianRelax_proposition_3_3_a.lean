-- Prove2me | Theorems.Thm_RockafellianRelax_proposition_3_3_a
-- name    : RockafellianRelax.proposition_3_3_a
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:26.76735+00:00
-- url     : https://prove2.me/theorems/f43efb1f-3a51-4de5-85ab-c5ec8d47dfa6
-- title:
--   Proposition 3.3 (first claim) — exactness implies (3.3): $x^\star \in \operatorname{argmin}\varphi \Rightarrow (0,x^\star)$ minimizes the relaxation
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi : \mathbb R^n \to \overline{\mathbb R}$. If $f$ is exact, supported by $\bar y \in \mathbb R^m$, then for every $x^\star$,
--
--   $$
--   x^\star \in \operatorname*{argmin}_x \varphi(x) \implies (0, x^\star) \in \operatorname*{argmin}_{u,x}\bigl\{f(u,x) - \langle\bar y, u\rangle\bigr\}. \tag{3.3}
--   $$
--
--   Differences from the source:
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.3, p.7, (3.3)

import Mathlib
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Proposition 3.3, first claim: exactness gives (3.3).** Royset, Chen & Eckstrand,
arXiv:2204.04762v4, Proposition 3.3, p.7: "Suppose f : ℝᵐ×ℝⁿ → R̄ is a Rockafellian for the problem
(3.1) of minimizing φ : ℝⁿ → R̄. If f is exact, supported by ȳ, then
x⋆ ∈ argmin_x φ(x) =⇒ (0, x⋆) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩. (3.3)"

**Formalization Note.** `IsExact f φ ȳ` includes that `f` is a Rockafellian for `φ`. -/
theorem proposition_3_3_a {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hex : IsExact f φ ybar) :
    ∀ xs : Fin n → ℝ, xs ∈ argmin φ → ((0 : Fin m → ℝ), xs) ∈ argmin (tilt f ybar) := by sorry

end RockafellianRelax
