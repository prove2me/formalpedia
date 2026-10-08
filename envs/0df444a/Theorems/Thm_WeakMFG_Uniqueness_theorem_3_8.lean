-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_theorem_3_8
-- name    : WeakMFG.Uniqueness.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:45.279036+00:00
-- url     : https://prove2.me/theorems/2ecc78d5-0b7e-4d66-b0a3-4b415aa52bb6
-- title:
--   Theorem 3.8 — under (U) the mean field game has at most one solution
-- statement:
--   Consider the mean field game in the weak formulation of Carmona and Lacker under the standing assumptions (S): a driftless state $dX_t=\sigma(t,X)dW_t$, $X_0=\xi$, rewards $f(t,X,\mu,q_t,\alpha_t)$ and $g(X,\mu)$, and the controlled laws $P^{\mu,\alpha}$ obtained by Girsanov's theorem with drift $b(t,X,\mu,\alpha_t)$. Assume moreover Assumption (U):
--
--   1. the maximizer of the Hamiltonian $h(t,x,\mu,q,z,a)=f(t,x,\mu,q,a)+z\cdot\sigma^{-1}b(t,x,\mu,a)$ over $a\in A$ is unique;
--   2. $b=b(t,x,a)$ has no mean field term;
--   3. $f(t,x,\mu,q,a)=f_1(t,x,\mu)+f_2(t,\mu,q)+f_3(t,x,a)$;
--   4. the Lasry–Lions monotonicity condition holds: for all $\mu,\mu'\in\mathcal P_\psi(\mathcal C)$,
--   $$\int_{\mathcal C}\Big[g(x,\mu)-g(x,\mu')+\int_0^T\big(f_1(t,x,\mu)-f_1(t,x,\mu')\big)dt\Big](\mu-\mu')(dx)\le0.$$
--
--   **Theorem 3.8.** There is at most one solution of the MFG: if $(\mu^1,q^1)$ and $(\mu^2,q^2)$ are solutions in the sense of Definition 3.4, then
--   $$\mu^1=\mu^2\qquad\text{and}\qquad q^1_t=q^2_t\ \text{ for almost every }t\in[0,T].$$
--
--   Combined with the existence theorem (Theorem 3.5) this gives existence and uniqueness (Corollary 3.9). The weak formulation needs no Lipschitz continuity of the coefficients in the state or the measure.
--
--   **Formalization Note.** The standing assumptions are hypotheses, with these encodings: an abstract base space carrying $(\xi,W)$ instead of the canonical one; "strong solution" of the state equation in the $L^2$ Itô sense; nonsingular $\sigma$ as matrix invertibility; monotone $\rho$. Two hypotheses are added and disclosed: joint measurability of $(t,x,q,a)\mapsto f(t,x,\mu,q,a)$, which the reward functional presupposes, and, in (U.4), the integrability its integrals presuppose. Definition 3.4 constrains $q_t$ only for almost every $t$, so uniqueness of $q$ is up to a Lebesgue-null set of times.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.2, Theorem 3.8, p. 11

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **Theorem 3.8** (Carmona–Lacker, arXiv:1307.1152v2, §3.2, p. 11). Suppose (U) holds. Then
there is at most one solution of the MFG: if `(μ₁, q₁)` and `(μ₂, q₂)` both solve the MFG in the
sense of Definition 3.4, then `μ₁ = μ₂` and `q₁(t) = q₂(t)` for almost every `t ∈ [0, T]`.
**Formalization Note.** The standing assumptions (S) are hypotheses (`Standing`), with the
conventions D1 (abstract base space), D2 (L² Itô solution of (3.1)), D3 (nonsingular σ),
D4 (monotone ρ). (D5) `FJointMeas` adds joint measurability of the running reward in
`(t, x, q, a)`, which the reward functional presupposes. (U.4) carries the integrability its
integrals presuppose. Definition 3.4 constrains `q_t` only for almost every `t`, so `q` is
identified up to a Lebesgue-null set of times. -/
theorem theorem_3_8 {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T)
    (hS : Standing B A σ b f g X Xp) (hD5 : FJointMeas A f)
    (hU : AssumptionU A σ b f g)
    (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : ℝ≥0 → PA A)
    (h₁ : IsMFGSolution B A σ b f g Xp μ₁ q₁) (h₂ : IsMFGSolution B A σ b f g Xp μ₂ q₂) :
    μ₁ = μ₂ ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), q₁ t.toNNReal = q₂ t.toNNReal := by sorry

end WeakMFG.Uniqueness
