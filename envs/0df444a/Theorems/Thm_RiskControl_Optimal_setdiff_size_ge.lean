-- Prove2me | Theorems.Thm_RiskControl_Optimal_setdiff_size_ge
-- name    : RiskControl.Optimal.setdiff_size_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:53.045979+00:00
-- url     : https://prove2.me/theorems/9598195b-11ba-427c-b670-9396e6a2eb49
-- title:
--   Proof of Theorem 8, p. 27, displays 5–7 — on the set differences, E[ℓ|X] < −λ vs ≥ −λ gives E|T′(X)∖T_λ(X)| ≥ E|T_λ(X)∖T′(X)|
-- statement:
--   Let $P$ be a measure on $\mathcal X \times \mathcal Y$ with marginal $P_X$ on $\mathcal X$, let $\kappa$ be a Markov kernel from $\mathcal X$ to $\mathcal Y$, let $\mu$ be a measure on $\mathcal Z$ and $\ell : \mathcal Y \times \mathcal Z \to [0, \infty)$ measurable, and write $\mathbb E[\ell(Y; z) \mid X = x] = \int \ell(y, z)\, d\kappa(x)(y)$. Let $\lambda < 0$, let $\mathcal T_\lambda(x) = \{z : \mathbb E[\ell(Y; z) \mid X = x] \ge -\lambda\}$ be the predictor (11), and let $\mathcal T'$ be a set-valued predictor with measurable graph. If
--   $$\mathbb E\Big[\int_{z \in \mathcal T'(X) \setminus \mathcal T_\lambda(X)} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)\Big] \ge \mathbb E\Big[\int_{z \in \mathcal T_\lambda(X) \setminus \mathcal T'(X)} \mathbb E[\ell(Y; z) \mid X]\, d\mu(z)\Big],$$
--   with $X \sim P_X$, then
--   $$\mathbb E\big[|\mathcal T'(X) \setminus \mathcal T_\lambda(X)|\big] \ge \mathbb E\big[|\mathcal T_\lambda(X) \setminus \mathcal T'(X)|\big],$$
--   where $|\cdot|$ is the measure $\mu$.
--
--   This is the passage from the fifth to the seventh display of the proof of Theorem 8: on $\mathcal T'(x) \setminus \mathcal T_\lambda(x)$ the conditional expected cost is below $-\lambda$ and on $\mathcal T_\lambda(x) \setminus \mathcal T'(x)$ it is at least $-\lambda$.
--
--   **Formalization Note** The paper allows $\lambda \le 0$; the step needs $-\lambda > 0$ and is stated for $\lambda < 0$. The size $|\cdot|$ is $\mu$, as the sixth to seventh display of the proof requires. Integrals are lower Lebesgue integrals in $[0, \infty]$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Theorem 8, p. 27, fifth to seventh displays

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- Proof of Theorem 8, arXiv:2101.02703v3, p. 27, displays 5–7: if `λ < 0`, `𝒯′` has a measurable
graph and display 5 holds, i.e.
`𝔼[∫_{𝒯_λ(X) ∖ 𝒯′(X)} 𝔼[ℓ(Y; z) | X] dμ] ≤ 𝔼[∫_{𝒯′(X) ∖ 𝒯_λ(X)} 𝔼[ℓ(Y; z) | X] dμ]`, then
`𝔼[|𝒯_λ(X) ∖ 𝒯′(X)|] ≤ 𝔼[|𝒯′(X) ∖ 𝒯_λ(X)|]`, sizes measured by `μ` and `X ~ P.fst`. -/
theorem setdiff_size_ge {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵)
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ]
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (h5 : ∫⁻ x, ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ ∂P.fst
      ≤ ∫⁻ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ∂P.fst) :
    ∫⁻ x, μ (thresholdSet κ ℓ lam x \ T' x) ∂P.fst
      ≤ ∫⁻ x, μ (T' x \ thresholdSet κ ℓ lam x) ∂P.fst := by sorry

end RiskControl.Optimal
