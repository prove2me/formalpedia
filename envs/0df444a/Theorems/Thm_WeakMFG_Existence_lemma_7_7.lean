-- Prove2me | Theorems.Thm_WeakMFG_Existence_lemma_7_7
-- name    : WeakMFG.Existence.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:57.912415+00:00
-- url     : https://prove2.me/theorems/2caab84e-4cbb-4617-b841-299c49cde9cf
-- title:
--   Lemma 7.7 — the densities dΦ(µ, α)/d𝒳 have q-th moments bounded uniformly in (µ, α), |q| ≥ 1
-- statement:
--   Assume the standing assumptions (S). Let $\mathcal X=P\circ X^{-1}$ be the law of the driftless state and, for $\mu\in\mathcal P_\psi(\mathcal C)$ and $\alpha\in\mathbb A$, let $\Phi(\mu,\alpha)=P^{\mu,\alpha}\circ X^{-1}$ (the first component of the map $\Phi$ of §7). For every $q\in\mathbb R$ with $|q|\ge1$,
--   $$M_q:=\sup_{(\mu,\alpha)\in\mathcal P_\psi(\mathcal C)\times\mathbb A}\int\Big(\frac{d\Phi(\mu,\alpha)}{d\mathcal X}\Big)^q\,d\mathcal X<\infty .$$
--
--   The bounds $M_2$ and $M_{-1}$ define the set $\mathcal Q$ (7.6) that contains the range of $\Phi$ and is compact (Proposition 7.8).
--
--   **Formalization Note** $M_q$ is a supremum in $[0,\infty]$; it also runs over all versions of the density $dP^{\mu,\alpha}/dP$. The claim is the uniform bound (the supremum is finite), not finiteness for each $(\mu,\alpha)$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 7.7, (7.5), p. 24

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward
import Definitions.Def_WeakMFG_Existence_FixedPoint

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Lemma 7.7 (Carmona–Lacker, arXiv:1307.1152v2, p. 24): for any `q ∈ ℝ` with `|q| ≥ 1`,
`M_q := sup_{(μ, α) ∈ P_ψ(C) × 𝔸} ∫ (dΦ(μ, α)/d𝒳)^q d𝒳 < ∞` (7.5), where `𝒳 = P ∘ X⁻¹` and the
first component of `Φ(μ, α)` is `P^{μ,α} ∘ X⁻¹`. Formalization Note: `M_q` is an `ℝ≥0∞` supremum,
also over all density versions. -/
theorem lemma_7_7 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp) :
    ∀ q : ℝ, 1 ≤ |q| → Mq (A := A) B σ b Xp q < ⊤ := by sorry

end WeakMFG.Existence
