-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_fixed_point_identification
-- name    : WeakMFG.Uniqueness.fixed_point_identification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:53.332605+00:00
-- url     : https://prove2.me/theorems/4af8376b-a209-44ce-85d6-86a8797b1eda
-- title:
--   §7.3 (p. 30) — an MFG solution's optimal control lies in $\mathbb A(\mu, q)$, a singleton a.e. under (U.1)
-- statement:
--   Assume the standing assumptions (S), the joint measurability of the running reward, and (U.1). Let $\mu\in\mathcal P_\psi(\mathcal C)$ and a measurable $q:[0,T]\to\mathcal P(A)$ form a solution of the MFG with witness $\alpha$ (Definition 3.4): $\alpha\in\mathbb A$ is optimal, $P^{\mu,\alpha}\circ X^{-1}=\mu$ and $P^{\mu,\alpha}\circ\alpha_t^{-1}=q_t$ for a.e. $t$. Let $(Y,Z)$ solve the BSDE (7.1) for $(\mu,q)$. Then:
--
--   1. $\alpha\in\mathbb A(\mu,q)$, that is,
--   $$\alpha_t\in A(t,X,\mu,q_t,Z_t)\qquad dt\times dP\text{-a.e. on }[0,T]\times\Omega;$$
--   2. every $\beta\in\mathbb A(\mu,q)$ coincides with $\alpha$ $dt\times dP$-a.e. on $[0,T]\times\Omega$.
--
--   The first part says that a solution of the MFG is a fixed point of the set-valued map $(\mu,\nu)\mapsto\Phi(\mu,\mathbb A(\mu,\nu))$; the second that under (U.1) this map is single-valued. It is the starting point of the uniqueness proof (§7.3).
--
--   **Formalization Note.** Part 1 is the content of "that is, they are fixed points of the (single-valued) function $\Phi(\cdot,\mathbb A(\cdot))$" (p. 30), which the paper asserts without a displayed argument; it is a conclusion here, not a hypothesis. Conventions as in the definitions: abstract base space, $L^2$ Itô solution of (3.1), densities quantified over versions, joint measurability of $f$ added.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.3, proof of Theorem 3.8, p. 30, first paragraph; with §7, p. 22 (paragraph after (7.4)) and Remark 7.2

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU
import Definitions.Def_WeakMFG_Uniqueness_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **§7.3, proof of Theorem 3.8, p. 30, with §7, p. 22 (Remark 7.2)** (Carmona–Lacker,
arXiv:1307.1152v2). A solution of the MFG is a fixed point of `Φ(·, 𝔸(·))`, and under (U.1) the
set `𝔸(μ, ν)` is a singleton up to `dt × dP`-null sets. Precisely: let `α` witness that `(μ, q)`
solves the MFG (Definition 3.4) and let `(Y, Z)` solve the BSDE (7.1) for `(μ, q)`. Then
(a) `α ∈ 𝔸(μ, q)`: `α_t ∈ A(t, X, μ, q_t, Z_t)` for `dt × dP`-a.e. `(t, ω)` (an optimal control
maximizes the Hamiltonian); and (b) under (U.1), every `β ∈ 𝔸(μ, q)` agrees with `α`
`dt × dP`-a.e. on `[0, T] × Ω`.
**Formalization Note.** (a) is the content of "that is, they are fixed points of the
(single-valued) function `Φ(·, 𝔸(·))`" (p. 30); it is a conclusion, not a hypothesis. Conventions
D1–D5 as in `theorem_3_8`. -/
theorem fixed_point_identification {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T)
    (hS : Standing B A σ b f g X Xp) (hD5 : FJointMeas A f)
    (hU1 : U1 A σ b f)
    (μ : Ppsi ψ) (q : ℝ≥0 → PA A) (hq : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q)
    (α : ℝ≥0 → Ω → EA) (hα : IsMFGWitness B A σ b f g Xp μ q α)
    (Y : ℝ≥0 → Ω → Unit → ℝ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ)
    (hYZ : SolvesBSDE71 B A σ b f g Xp μ q Y Z) :
    InAset B A σ b f Xp μ q Z α ∧
      ∀ β : ℝ≥0 → Ω → EA, InAset B A σ b f Xp μ q Z β →
        ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod B.P),
          β p.1.toNNReal p.2 = α p.1.toNNReal p.2 := by sorry

end WeakMFG.Uniqueness
