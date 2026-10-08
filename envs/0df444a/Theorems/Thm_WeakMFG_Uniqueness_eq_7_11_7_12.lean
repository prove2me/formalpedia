-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_eq_7_11_7_12
-- name    : WeakMFG.Uniqueness.eq_7_11_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:33.311226+00:00
-- url     : https://prove2.me/theorems/1d59a197-91db-4ab0-b158-2cbebd1e9411
-- title:
--   (7.11)–(7.12) — Hamiltonian maximization bounds $f^1 - f^2 + z\cdot(b^1 - b^2)$, strictly under (U.1)
-- statement:
--   Assume (S.1), (S.3), (U.2) $b(t,x,\mu,a)=b_0(t,x,a)$, and the decomposition (U.3) $f(t,x,\mu,q,a)=f_1(t,x,\mu)+f_2(t,\mu,q)+f_3(t,x,a)$. Fix $t$, $x\in\mathcal C$, $z\in\mathbb R^d$, $\mu^1,\mu^2\in\mathcal P_\psi(\mathcal C)$, $q^1,q^2\in\mathcal P(A)$, a control value $a^1\in A$, and a maximizer $a^2\in A(t,x,\mu^2,q^2,z)$ of the Hamiltonian. With $\theta(a)=\sigma^{-1}b_0(t,x,a)$ and $\Delta f_1 = f_1(t,x,\mu^1)-f_1(t,x,\mu^2)$,
--   $$f(t,x,\mu^1,q^1,a^1)-f(t,x,\mu^2,q^2,a^2)+z\cdot\big(\theta(a^1)-\theta(a^2)\big)\le\Delta f_1+f_2(t,\mu^1,q^1)-f_2(t,\mu^2,q^2),$$
--   and if moreover (U.1) holds and $a^1\neq a^2$, the inequality is strict.
--
--   With $z=Z^2_t$ and $a^i=\alpha^i_t$ this is (7.11); exchanging the roles of the indices (with $z=Z^1_t$ and $a^1$ the maximizer) and rearranging gives (7.12). The strict form is what turns (7.13) into the almost-everywhere equality of the two optimal controls.
--
--   **Formalization Note.** The statement is pointwise in $(t,x,z)$. The strict clause is the use the paper makes of (U.1) on p. 31 ("(U.1) implies that the inequalities (7.11) and (7.12) are strict").
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.3, proof of Theorem 3.8, (7.11)–(7.12), p. 31

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **(7.11)–(7.12)** (Carmona–Lacker, arXiv:1307.1152v2, §7.3, p. 31), pointwise. Assume (S.1),
(S.3), (U.2) `b(t, x, μ, a) = b₀(t, x, a)` and the decomposition (U.3)
`f(t, x, μ, q, a) = f₁(t, x, μ) + f₂(t, μ, q) + f₃(t, x, a)`. Fix `(t, x, z)`, `μ¹, μ²`, `q¹, q²`,
`a¹ ∈ A`, and let `a²` maximize the Hamiltonian, `a² ∈ A(t, x, μ², q², z)`. Then, with
`θ(a) = σ⁻¹b₀(t, x, a)` and `Δf₁ = f₁(t, x, μ¹) − f₁(t, x, μ²)`,
`f(t, x, μ¹, q¹, a¹) − f(t, x, μ², q², a²) + z · (θ(a¹) − θ(a²)) ≤ Δf₁ + f₂(t, μ¹, q¹) − f₂(t, μ², q²)`
(this is (7.11) with `z = Z²_t`, `aⁱ = αⁱ_t`), and under (U.1) the inequality is strict when
`a¹ ≠ a²`. Inequality (7.12) is the same statement with the indices exchanged (`z = Z¹_t`, `a¹`
the maximizer), rearranged. -/
theorem eq_7_11_7_12 {d : ℕ} {T : ℝ≥0}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (hS1 : S1 A σ b) (hS3 : S3 A f g)
    (b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ)) (hb₀ : ∀ t x μ a, b t x μ a = b₀ t x a)
    (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₂ : ℝ≥0 → Ppsi ψ → PA A → ℝ)
    (f₃ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → ℝ) (hdec : IsU3Decomp f f₁ f₂ f₃)
    (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (z : Fin d → ℝ) (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : PA A) (a₁ a₂ : EA)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ Amax A σ b f t x μ₂ q₂ z) :
    (f t x μ₁ q₁ a₁ - f t x μ₂ q₂ a₂ + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a₁ - (σ t x)⁻¹ *ᵥ b₀ t x a₂) ≤
        f₁ t x μ₁ - f₁ t x μ₂ + f₂ t μ₁ q₁ - f₂ t μ₂ q₂) ∧
    (U1 A σ b f → a₁ ≠ a₂ →
      f t x μ₁ q₁ a₁ - f t x μ₂ q₂ a₂ + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a₁ - (σ t x)⁻¹ *ᵥ b₀ t x a₂) <
        f₁ t x μ₁ - f₁ t x μ₂ + f₂ t μ₁ q₁ - f₂ t μ₂ q₂) := by sorry

end WeakMFG.Uniqueness
