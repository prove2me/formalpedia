-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_alpha_ae_eq
-- name    : WeakMFG.Uniqueness.alpha_ae_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:18.479988+00:00
-- url     : https://prove2.me/theorems/92030b3b-b703-4aca-bfe1-c1f7ae2972a4
-- title:
--   §7.3 (p. 31) — the optimal controls of two MFG solutions agree $\mathcal L\times P$-a.e.
-- statement:
--   Assume the standing assumptions (S), the joint measurability of the running reward, and Assumption (U). Let $\alpha^1,\alpha^2$ witness that $(\mu^1,q^1)$ and $(\mu^2,q^2)$ are solutions of the MFG (Definition 3.4, with $q^i$ measurable). Then
--   $$\alpha^1_t(\omega)=\alpha^2_t(\omega)\qquad\text{for }\mathcal L\times P\text{-almost every }(t,\omega)\in[0,T]\times\Omega,$$
--   where $\mathcal L$ is Lebesgue measure.
--
--   Once the controls agree, so do the densities $dP^{\mu^i,\alpha^i}/dP$ (under (U.2) the drift does not see $\mu$), hence $\mu^1=P^{\mu^1,\alpha^1}\circ X^{-1}=P^{\mu^2,\alpha^2}\circ X^{-1}=\mu^2$ and $q^1_t=q^2_t$ for a.e. $t$: this is the last step before Theorem 3.8.
--
--   **Formalization Note.** The page prints "Thus $\alpha^1\neq\alpha^2$ must hold $\mathcal L\times P$-a.e."; the argument (a contradiction with $\alpha^1\ne\alpha^2$ on a set of positive measure) proves $\alpha^1=\alpha^2$ almost everywhere, which is what is stated.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.3, proof of Theorem 3.8, p. 31, last paragraph

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **§7.3, proof of Theorem 3.8, p. 31: `α¹ = α²` a.e.** (Carmona–Lacker, arXiv:1307.1152v2).
Suppose (U) holds, and let `α¹, α²` witness that `(μ¹, q¹)` and `(μ², q²)` solve the MFG. Then
`α¹_t(ω) = α²_t(ω)` for `𝓛 × P`-almost every `(t, ω) ∈ [0, T] × Ω`.
**Formalization Note.** The page prints "Thus `α¹ ≠ α²` must hold `𝓛 × P`-a.e."; the argument (a
contradiction with `α¹ ≠ α²` on a set of positive measure) proves `α¹ = α²` a.e., which is what is
stated. Conventions D1–D5 as in `theorem_3_8`. -/
theorem alpha_ae_eq {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T)
    (hS : Standing B A σ b f g X Xp) (hD5 : FJointMeas A f)
    (hU : AssumptionU A σ b f g)
    (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : ℝ≥0 → PA A)
    (hq₁ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₁)
    (hq₂ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₂)
    (α₁ α₂ : ℝ≥0 → Ω → EA)
    (hα₁ : IsMFGWitness B A σ b f g Xp μ₁ q₁ α₁) (hα₂ : IsMFGWitness B A σ b f g Xp μ₂ q₂ α₂) :
    ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod B.P),
      α₁ p.1.toNNReal p.2 = α₂ p.1.toNNReal p.2 := by sorry

end WeakMFG.Uniqueness
