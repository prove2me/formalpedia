-- Prove2me | Theorems.Thm_RockafellianRelax_proposition_3_3_d
-- name    : RockafellianRelax.proposition_3_3_d
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:23.02492+00:00
-- url     : https://prove2.me/theorems/b4a9b0cc-e3a8-4796-b558-f598de51bfdd
-- title:
--   Proposition 3.3 (fourth claim) — under attainment, (3.4) implies strict exactness
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi : \mathbb R^n \to \overline{\mathbb R}$, with min-value function $\mathcal V(u) = \inf_x f(u,x)$, and $\bar y \in \mathbb R^m$. Suppose
--
--   1. $\operatorname{argmin}_{u,x}\{f(u,x) - \langle\bar y,u\rangle\} \ne \emptyset$;
--   2. $\operatorname{argmin}_x f(u,x) \ne \emptyset$ for every $u \in \operatorname{dom}\mathcal V = \{u \mid \mathcal V(u) < \infty\}$;
--   3. (3.4) holds: every $(u^\star,x^\star) \in \operatorname{argmin}_{u,x}\{f(u,x) - \langle\bar y,u\rangle\}$ has $u^\star = 0$ and $x^\star \in \operatorname{argmin}_x\varphi(x)$.
--
--   Then $f$ is strictly exact, supported by $\bar y$.
--
--   Differences from the source:
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
--   - encoding: dom 𝒱 = {u | 𝒱(u) < ∞} → AubinLipschitz.effDom (minValue f) = {u | 𝒱(u) ≠ ⊤}; reason: the same set, since every value is ≤ ⊤
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.3, p.8

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Proposition 3.3, fourth claim: (3.4) gives strict exactness.** Royset, Chen & Eckstrand,
arXiv:2204.04762v4, Proposition 3.3, p.8: "When argmin_{u,x} f(u, x) − ⟨ȳ, u⟩ ≠ ∅ and
argmin_x f(u, x) ≠ ∅ for all u ∈ dom 𝒱, then (3.4) conversely implies strict exactness."

**Formalization Note.** (3.4) is `(u⋆, x⋆) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩ ⟹ u⋆ = 0 ∧
x⋆ ∈ argmin φ` for all `(u⋆, x⋆)`; `dom 𝒱 = {u | 𝒱(u) < +∞}`. -/
theorem proposition_3_3_d {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ)
    (hne : (argmin (tilt f ybar)).Nonempty)
    (hsec : ∀ u ∈ AubinLipschitz.effDom (minValue f),
      (argmin (fun x : Fin n → ℝ => f (u, x))).Nonempty)
    (h34 : ∀ (us : Fin m → ℝ) (xs : Fin n → ℝ), (us, xs) ∈ argmin (tilt f ybar) →
      us = 0 ∧ xs ∈ argmin φ) :
    IsStrictlyExact f φ ybar := by sorry

end RockafellianRelax
