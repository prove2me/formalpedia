-- Prove2me | Theorems.Thm_RiskControl_Optimal_lintegral_condLoss
-- name    : RiskControl.Optimal.lintegral_condLoss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:55.733481+00:00
-- url     : https://prove2.me/theorems/8b9f829f-091b-411c-8b98-bcee7b5f0bc7
-- title:
--   Proof of Theorem 8, p. 27, displays 3–4 — E[∫_{T(X)} ℓ(Y; z) dμ(z)] = E[∫_{T(X)} E[ℓ(Y; z) | X] dμ(z)]
-- statement:
--   Let $P$ be a probability measure on $\mathcal X \times \mathcal Y$, the law of $(X, Y)$, with marginal $P_X$, and let $\kappa$ be a Markov kernel from $\mathcal X$ to $\mathcal Y$ that disintegrates $P$, so that $\kappa(x)$ is the conditional law of $Y$ given $X = x$. Let $\mu$ be a finite measure on $\mathcal Z$, let $\ell : \mathcal Y \times \mathcal Z \to [0, \infty)$ be measurable, and let $\mathcal A : \mathcal X \to 2^{\mathcal Z}$ be a set-valued predictor whose graph $\{(x, z) : z \in \mathcal A(x)\}$ is measurable. Then
--   $$\mathbb E\Big[\int_{z \in \mathcal A(X)} \ell(Y; z)\, d\mu(z)\Big] = \mathbb E\Big[\int_{z \in \mathcal A(X)} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)\Big],$$
--   where $\mathbb E[\ell(Y; z) \mid X = x] = \int \ell(y, z)\, d\kappa(x)(y)$.
--
--   This is the step of the proof of Theorem 8 that moves the conditional expectation inside the $\mu$-integral; the proof applies it to $\mathcal T'$, $\mathcal T_\lambda$, their complements and their set differences.
--
--   **Formalization Note** The page writes the left side as $\mathbb E[\mathbb E[\int_{z \in \mathcal A(X)} \ell(Y; z)\, d\mu(z) \mid X]]$; by the tower property this is the plain expectation stated here. Integrals are lower Lebesgue integrals in $[0, \infty]$. The measurable graph is needed for both sides to be integrals of measurable functions; the page leaves it implicit.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem 8, p. 27, third and fourth displays

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- Proof of Theorem 8, arXiv:2101.02703v3, p. 27, displays 3–4: for any set-valued predictor
`A : 𝒳 → 2^𝒵` with a measurable graph,
`𝔼[𝔼[∫_{z ∈ A(X)} ℓ(Y; z) dμ(z) | X]] = 𝔼[∫_{z ∈ A(X)} 𝔼[ℓ(Y; z) | X] dμ(z)]`, where the outer
`𝔼[𝔼[· | X]] = 𝔼[·]` is taken under `P` and `𝔼[ℓ(Y; z) | X = x]` is `condLoss κ ℓ x z` for a
Markov kernel `κ` disintegrating `P`. -/
theorem lintegral_condLoss {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (A : 𝒳 → Set 𝒵) (hA : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ A q.1}) :
    ∫⁻ p, ∫⁻ z in A p.1, (ℓ p.2 z : ℝ≥0∞) ∂μ ∂P
      = ∫⁻ x, ∫⁻ z in A x, condLoss κ ℓ x z ∂μ ∂P.fst := by sorry

end RiskControl.Optimal
