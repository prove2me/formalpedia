-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_5_1
-- name    : RockafellianRelax.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:19:56.603011+00:00
-- url     : https://prove2.me/theorems/9fdd8778-99cb-5166-961e-58e44d9a9905
-- title:
--   Theorem 5.1 — first-order optimality condition from an exact Rockafellian
-- statement:
--   Let $\varphi:\mathbb R^n\to\overline{\mathbb R}$ be proper and let $f:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ be an exact Rockafellian for minimizing $\varphi$, supported by $\bar y\in\mathbb R^m$. Let $\partial$ be the general (limiting) subdifferential of Rockafellar–Wets, empty at points where the function is not finite. Then
--
--   $$
--   x^\star\in\operatorname*{argmin}_x\varphi(x)\ \Longrightarrow\ \exists\,u^\star\in\mathbb R^m:\ (\bar y,0)\in\partial f(u^\star,x^\star).
--   $$
--
--   Exactness thus serves as a qualification condition for a first-order necessary optimality condition. The function $f$ need not be proper, lower semicontinuous or convex.
--
--   **Formalization Note** The argmin carries the domain condition of the paper, and subgradients are paired by the sum of the two dot products.
--
--   Differences from the source:
--
--   - encoding: ∂f in the general sense of [51], empty where f is not finite → the published limiting subdifferential on EuclideanSpace ℝ (Fin m ⊕ Fin n), pulled back, with f(z) ≠ ⊥ added; reason: this is Rockafellar–Wets Definition 8.3 at finite points and is empty elsewhere
--   - encoding: ℝᵐ × ℝⁿ, R̄ → (Fin m → ℝ) × (Fin n → ℝ), EReal; reason: Lean conventions with the same instances
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 5.1, p.24

import Mathlib
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_Supplement_IsProper
import Definitions.Def_RockafellianRelax_Supplement_subdiff

namespace RockafellianRelax.Supplement

/-- **Theorem 5.1 (first-order optimality condition).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 5.1, p.24: "For the problem of
minimizing a proper function φ : ℝⁿ → R̄, suppose that f : ℝᵐ × ℝⁿ → R̄ is an exact Rockafellian
supported by ȳ ∈ ℝᵐ. Then, the following necessary first-order optimality condition holds:
x⋆ ∈ argmin_x φ(x) ⟹ ∃u⋆ ∈ ℝᵐ such that (ȳ, 0) ∈ ∂f(u⋆, x⋆)."

**Formalization Note.** `∂` is the general (limiting) subdifferential `subdiff`, empty where `f` is
not finite, and `argmin` carries the domain condition of p.6. `f` is not assumed proper, lsc or
convex. The existential `u⋆` is kept as printed. -/
theorem theorem_5_1 {m n : ℕ} (φ : (Fin n → ℝ) → EReal) (hφ : IsProper φ)
    (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (ybar : Fin m → ℝ) (hex : IsExact f φ ybar) :
    ∀ xs : Fin n → ℝ, xs ∈ argmin φ →
      ∃ us : Fin m → ℝ, (ybar, (0 : Fin n → ℝ)) ∈ subdiff f (us, xs) := by sorry

end RockafellianRelax.Supplement
