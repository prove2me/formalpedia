-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_eq_7_9_7_10
-- name    : WeakMFG.Uniqueness.eq_7_9_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:05.195693+00:00
-- url     : https://prove2.me/theorems/ab62f7bd-f9ae-4dd1-88c1-038866d918a3
-- title:
--   (7.9)–(7.10) — $E[Y^1_0 - Y^2_0]$ under $P^{\mu^1,\alpha^1}$ and under $P^{\mu^2,\alpha^2}$
-- statement:
--   Assume the standing assumptions (S), the joint measurability of the running reward, and (U.2): $b(t,x,\mu,a)=b_0(t,x,a)$. For $i=1,2$ let $\mu^i\in\mathcal P_\psi(\mathcal C)$, let $q^i:[0,T]\to\mathcal P(A)$ be measurable, let $(Y^i,Z^i)$ solve the BSDE (7.1) for $(\mu^i,q^i)$, let $\alpha^i\in\mathbb A(\mu^i,q^i)$, and let $D^i$ be a version of $dP^{\mu^i,\alpha^i}/dP$, with $E^{\mu^i,\alpha^i}[F]=E[D^iF]$. Write
--   $$f^i_t = f(t,X,\mu^i,q^i_t,\alpha^i_t),\qquad b^i_t=\sigma^{-1}b_0(t,X,\alpha^i_t),\qquad \Delta g(X)=g(X,\mu^1)-g(X,\mu^2).$$
--   Then
--   $$E\big[Y^1_0-Y^2_0\big] = E^{\mu^1,\alpha^1}\Big[\Delta g(X)+\int_0^T\big(f^1_t-f^2_t+Z^2_t\cdot(b^1_t-b^2_t)\big)dt\Big] \tag{7.9}$$
--   $$\phantom{E\big[Y^1_0-Y^2_0\big]} = E^{\mu^2,\alpha^2}\Big[\Delta g(X)+\int_0^T\big(f^1_t-f^2_t+Z^1_t\cdot(b^1_t-b^2_t)\big)dt\Big]. \tag{7.10}$$
--
--   These two representations of the same number are the bridge between the two solutions in the uniqueness proof: each is compared with the Lasry–Lions quantity of (U.4) through the Hamiltonian inequalities (7.11)–(7.12).
--
--   **Formalization Note.** The identities hold for every version of the densities. Only membership $\alpha^i\in\mathbb A(\mu^i,q^i)$ is assumed of the controls. In the Lean statement $f^i$ is named `rewⁱ` and $b^i$ is named `driftⁱ`; $Y^i_0$ is the value of the scalar BSDE solution at time $0$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.3, proof of Theorem 3.8, (7.9)–(7.10), pp. 30–31

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU
import Definitions.Def_WeakMFG_Uniqueness_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **(7.9)–(7.10)** (Carmona–Lacker, arXiv:1307.1152v2, §7.3, pp. 30–31). Assume (U.2),
`b(t, x, μ, a) = b₀(t, x, a)`. For `i = 1, 2` let `(Yⁱ, Zⁱ)` solve the BSDE (7.1) for `(μⁱ, qⁱ)`, let
`αⁱ ∈ 𝔸(μⁱ, qⁱ)`, and let `Dⁱ` be a version of `dP^{μⁱ,αⁱ}/dP`. With `fⁱ_t = f(t, X, μⁱ, qⁱ_t, αⁱ_t)`,
`bⁱ_t = σ⁻¹b₀(t, X, αⁱ_t)` and `Δg(X) = g(X, μ¹) − g(X, μ²)`,
`E[Y¹₀ − Y²₀] = E^{μ¹,α¹}[Δg(X) + ∫₀ᵀ (f¹_t − f²_t + Z²_t · (b¹_t − b²_t)) dt]` (7.9)
`= E^{μ²,α²}[Δg(X) + ∫₀ᵀ (f¹_t − f²_t + Z¹_t · (b¹_t − b²_t)) dt]` (7.10),
where `E^{μⁱ,αⁱ}[F] = E[Dⁱ F]`. In the Lean statement `rewⁱ` is `fⁱ` and `driftⁱ` is `bⁱ`.
**Formalization Note.** Conventions D1–D6 as in `theorem_3_8`; the claim holds for every version
`Dⁱ` of the densities. -/
theorem eq_7_9_7_10 {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T)
    (hS : Standing B A σ b f g X Xp) (hD5 : FJointMeas A f)
    (b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ)) (hb₀ : ∀ t x μ a, b t x μ a = b₀ t x a)
    (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : ℝ≥0 → PA A)
    (hq₁ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₁)
    (hq₂ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₂)
    (Y₁ Y₂ : ℝ≥0 → Ω → Unit → ℝ) (Z₁ Z₂ : Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (hYZ₁ : SolvesBSDE71 B A σ b f g Xp μ₁ q₁ Y₁ Z₁)
    (hYZ₂ : SolvesBSDE71 B A σ b f g Xp μ₂ q₂ Y₂ Z₂)
    (α₁ α₂ : ℝ≥0 → Ω → EA)
    (hα₁ : InAset B A σ b f Xp μ₁ q₁ Z₁ α₁) (hα₂ : InAset B A σ b f Xp μ₂ q₂ Z₂ α₂)
    (D₁ D₂ : Ω → ℝ) (hD₁ : IsDensity B σ b Xp μ₁ α₁ D₁) (hD₂ : IsDensity B σ b Xp μ₂ α₂ D₂) :
    let Δg : Ω → ℝ := fun ω => g (Xp ω) μ₁ - g (Xp ω) μ₂
    let rew₁ : ℝ≥0 → Ω → ℝ := fun t ω => f t (Xp ω) μ₁ (q₁ t) (α₁ t ω)
    let rew₂ : ℝ≥0 → Ω → ℝ := fun t ω => f t (Xp ω) μ₂ (q₂ t) (α₂ t ω)
    let drift₁ : ℝ≥0 → Ω → Fin d → ℝ := fun t ω => (σ t (Xp ω))⁻¹ *ᵥ b₀ t (Xp ω) (α₁ t ω)
    let drift₂ : ℝ≥0 → Ω → Fin d → ℝ := fun t ω => (σ t (Xp ω))⁻¹ *ᵥ b₀ t (Xp ω) (α₂ t ω)
    (∫ ω, (Y₁ 0 ω () - Y₂ 0 ω ()) ∂B.P =
        ∫ ω, D₁ ω * (Δg ω + ∫ t in Set.Icc (0 : ℝ) T,
          (rew₁ t.toNNReal ω - rew₂ t.toNNReal ω +
            zvec Z₂ t.toNNReal ω ⬝ᵥ (drift₁ t.toNNReal ω - drift₂ t.toNNReal ω))) ∂B.P) ∧
    (∫ ω, (Y₁ 0 ω () - Y₂ 0 ω ()) ∂B.P =
        ∫ ω, D₂ ω * (Δg ω + ∫ t in Set.Icc (0 : ℝ) T,
          (rew₁ t.toNNReal ω - rew₂ t.toNNReal ω +
            zvec Z₁ t.toNNReal ω ⬝ᵥ (drift₁ t.toNNReal ω - drift₂ t.toNNReal ω))) ∂B.P) := by sorry

end WeakMFG.Uniqueness
