-- Prove2me | Theorems.Thm_RockafellianRelax_proposition_3_3_c
-- name    : RockafellianRelax.proposition_3_3_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:14.04682+00:00
-- url     : https://prove2.me/theorems/17a85ace-1ef1-497b-a26e-9333cbc51809
-- title:
--   Proposition 3.3 (third claim) — strict exactness implies (3.4): minimizers of the relaxation have $u^\star = 0$ and $x^\star \in \operatorname{argmin}\varphi$
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi : \mathbb R^n \to \overline{\mathbb R}$. If $f$ is strictly exact, supported by $\bar y \in \mathbb R^m$, then for all $(u^\star, x^\star)$,
--
--   $$
--   (u^\star, x^\star) \in \operatorname*{argmin}_{u,x}\bigl\{f(u,x) - \langle\bar y, u\rangle\bigr\} \implies u^\star = 0,\ x^\star \in \operatorname*{argmin}_x\varphi(x). \tag{3.4}
--   $$
--
--   Under strict exactness, solving the relaxation solves the actual problem.
--
--   Differences from the source:
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.3, pp.7–8, (3.4)

import Mathlib
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Proposition 3.3, third claim: strict exactness gives (3.4).** Royset, Chen & Eckstrand,
arXiv:2204.04762v4, Proposition 3.3, pp.7–8: "Suppose f : ℝᵐ×ℝⁿ → R̄ is a Rockafellian for the
problem (3.1) of minimizing φ : ℝⁿ → R̄. … If f is strictly exact, supported by ȳ, then
(u⋆, x⋆) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩ =⇒ u⋆ = 0, x⋆ ∈ argmin_x φ(x). (3.4)"

**Formalization Note.** `IsStrictlyExact f φ ȳ` includes that `f` is a Rockafellian for `φ`. -/
theorem proposition_3_3_c {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hsx : IsStrictlyExact f φ ybar) :
    ∀ (us : Fin m → ℝ) (xs : Fin n → ℝ), (us, xs) ∈ argmin (tilt f ybar) →
      us = 0 ∧ xs ∈ argmin φ := by sorry

end RockafellianRelax
