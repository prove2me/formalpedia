-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_proposition_3_5
-- name    : RockafellianRelax.Supplement.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:18:47.897492+00:00
-- url     : https://prove2.me/theorems/58966791-3d5c-5716-b16e-944520f31520
-- title:
--   Proposition 3.5 — exactness from calmness
-- statement:
--   Let $f:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ be a Rockafellian for the problem of minimizing $\varphi:\mathbb R^n\to\overline{\mathbb R}$, that is $f(0,x)=\varphi(x)$ for all $x$. Let $\|\cdot\|$ be an arbitrary norm on $\mathbb R^m$, let $f_\theta(u,x)=f(u,x)+\theta\|u\|$, and let $\mathcal V(u)=\inf_xf(u,x)$. Then:
--
--   1. for every $\theta\ge0$, $f_\theta$ is a Rockafellian for the same problem;
--   2. if $\bar\theta\ge0$ satisfies
--   $$
--   \mathcal V(u)\ge\mathcal V(0)-\bar\theta\|u\|\qquad\text{for all }u\in\mathbb R^m, \tag{3.6}
--   $$
--   then $f_\theta$ is exact, supported by $\bar y=0$, for every $\theta\ge\bar\theta$;
--   3. under the same condition, $f_\theta$ is strictly exact, supported by $0$, for every $\theta>\bar\theta$ if $\mathcal V(0)\in\mathbb R$.
--
--   The proposition turns a calmness bound on the min-value function into exactness. The proof of Theorem 4.6 uses it.
--
--   **Formalization Note** The norm is a seminorm that vanishes only at $0$, and $\mathcal V(0)\in\mathbb R$ means that it is neither $+\infty$ nor $-\infty$.
--
--   Differences from the source:
--
--   - encoding: an arbitrary norm on ℝᵐ → Seminorm ℝ (Fin m → ℝ) that vanishes only at 0; reason: this is the definition of a norm
--   - encoding: ℝᵐ × ℝⁿ, R̄, 𝒱(0) ∈ ℝ → (Fin m → ℝ) × (Fin n → ℝ), EReal, 𝒱(0) different from ⊤ and from ⊥; reason: Lean conventions with the same instances
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.5 and display (3.6), p.8

import Mathlib
import Definitions.Def_RockafellianRelax_IsRockafellian
import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_IsStrictlyExact
import Definitions.Def_RockafellianRelax_minValue
import Definitions.Def_RockafellianRelax_Supplement_normPenalty

namespace RockafellianRelax.Supplement

/-- **Proposition 3.5 (exactness from calmness).** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Proposition 3.5, p.8: "Suppose that
f : ℝᵐ × ℝⁿ → R̄ is a Rockafellian for (3.1). Let ‖·‖ be an arbitrary norm on ℝᵐ. For any
θ ∈ [0, ∞), the function given by fθ(u, x) = f(u, x) + θ‖u‖ is also a Rockafellian for (3.1). If
there is θ̄ ∈ [0, ∞) such that 𝒱(u) ≥ 𝒱(0) − θ̄‖u‖ ∀u ∈ ℝᵐ, (3.6) then fθ is exact, supported by
ȳ = 0 as long as θ ≥ θ̄. The exactness is strict if θ > θ̄ and 𝒱(0) ∈ ℝ."

**Formalization Note.** An arbitrary norm is a `Seminorm ℝ (Fin m → ℝ)` that vanishes only at `0`.
The first claim does not assume (3.6). `𝒱(0) ∈ ℝ` is `≠ ⊤ ∧ ≠ ⊥` in `EReal`. -/
theorem proposition_3_5 {m n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ)
    (N : Seminorm ℝ (Fin m → ℝ)) (hN : ∀ u, N u = 0 → u = 0) :
    (∀ θ : ℝ, 0 ≤ θ → IsRockafellian (normPenalty f N θ) φ) ∧
      ∀ θbar : ℝ, 0 ≤ θbar →
        (∀ u : Fin m → ℝ, minValue f 0 - ((θbar * N u : ℝ) : EReal) ≤ minValue f u) →
        (∀ θ : ℝ, θbar ≤ θ → IsExact (normPenalty f N θ) φ 0) ∧
          (∀ θ : ℝ, θbar < θ → minValue f 0 ≠ ⊤ ∧ minValue f 0 ≠ ⊥ →
            IsStrictlyExact (normPenalty f N θ) φ 0) := by sorry

end RockafellianRelax.Supplement
