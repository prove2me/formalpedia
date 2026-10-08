-- Prove2me | Theorems.Thm_RiskControl_Optimal_theorem_8
-- name    : RiskControl.Optimal.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:32.6436+00:00
-- url     : https://prove2.me/theorems/e1965747-ad2b-4445-9e31-f18672ee5221
-- title:
--   Theorem 8, p. 13 — for λ < 0, T_λ(x) = {z : E[ℓ(Y; z) | X = x] ≥ −λ} has E|T_λ(X)| ≤ E|T′(X)| whenever R(T′) ≤ R(T_λ)
-- statement:
--   **Theorem 8 (Optimality of set predictors, generalized form).** Let $(X, Y)$ have law $P$ on $\mathcal X \times \mathcal Y$, with marginal $P_X$ and a regular conditional distribution $\kappa(x)$ of $Y$ given $X = x$. Let $\mu$ be a finite measure on a measurable space $\mathcal Z$ and $\ell : \mathcal Y \times \mathcal Z \to [0, \infty)$ measurable; $\ell(y, z)$ is the cost of not including $z$ in the prediction set when the true response is $y$. The loss of a set $\mathcal S \subseteq \mathcal Z$ is
--   $$L(y; \mathcal S) = \int_{z \in \mathcal S^c} \ell(y, z)\, d\mu(z),$$
--   and the risk of a set-valued predictor $\mathcal T : \mathcal X \to 2^{\mathcal Z}$ is $R(\mathcal T) = \mathbb E[L(Y; \mathcal T(X))]$. For $\lambda < 0$ let
--   $$\mathcal T_\lambda(x) = \{z : \mathbb E[\ell(Y; z) \mid X = x] \ge -\lambda\}. \tag{11}$$
--   If $\mathcal T'$ is any set-valued predictor (with measurable graph) such that $R(\mathcal T') \le R(\mathcal T_\lambda)$, then
--   $$\mathbb E\big[|\mathcal T_\lambda(X)|\big] \le \mathbb E\big[|\mathcal T'(X)|\big],$$
--   where $|\mathcal S| = \mu(\mathcal S)$.
--
--   The threshold sets (11) are thus the smallest on average among all set-valued predictors that are at least as accurate, for every loss of this integral form; Theorem 7 of the paper is the special case of a weighted miscoverage loss on a discrete label space.
--
--   **Formalization Note** The paper states the theorem for $\lambda \in \Lambda \subset (-\infty, 0]$; it is false at $\lambda = 0$ (take $\ell \equiv 0$ and $\mu(\mathcal Z) > 0$: then $\mathcal T_0(x) = \mathcal Z$ and $\mathcal T' \equiv \emptyset$ both have risk $0$, but $\mathbb E|\mathcal T'(X)| = 0 < \mu(\mathcal Z) = \mathbb E|\mathcal T_0(X)|$), and its proof divides by $-\lambda$; the statement is posed for $\lambda < 0$. The set size $|\cdot|$ is the measure $\mu$ of the loss, as the proof (p. 27) uses; p. 13 describes $|\cdot|$ as Lebesgue or counting measure in the context of Theorem 7. The conditional expectation $\mathbb E[\ell(Y; z) \mid X = x]$ is $\int \ell(y, z)\, d\kappa(x)(y)$ for a Markov kernel $\kappa$ with $P = P_X \otimes \kappa$; such a kernel exists, for instance, whenever $\mathcal Y$ is standard Borel. The predictor $\mathcal T'$ is required to have a measurable graph $\{(x, z) : z \in \mathcal T'(x)\}$, so that its risk and expected size are integrals of measurable functions; the page leaves this implicit. All integrals are lower Lebesgue integrals in $[0, \infty]$, so no integrability assumption is made.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Theorem 8, p. 13 (setting of §4.3 and (11), p. 13; risk R(𝒯), §2.1, p. 4); proof p. 27

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- Theorem 8 (Optimality of set predictors, generalized form), arXiv:2101.02703v3, p. 13, proof
p. 27. Let the loss be `L(y; 𝒮) = ∫_{z ∈ 𝒮ᶜ} ℓ(y, z) dμ(z)` for a nonnegative measurable `ℓ` and a
finite measure `μ`, let `κ` be a regular conditional distribution of `Y` given `X`
(`P.fst ⊗ₘ κ = P`), let `λ < 0` (the page allows `λ ≤ 0`; the claim fails at `λ = 0`), and let
`𝒯_λ(x) = {z : 𝔼[ℓ(Y; z) | X = x] ≥ −λ}` be (11). For every set-valued predictor `𝒯′` with a
measurable graph and `R(𝒯′) ≤ R(𝒯_λ)`, `𝔼[|𝒯_λ(X)|] ≤ 𝔼[|𝒯′(X)|]`, sizes measured by `μ`. -/
theorem theorem_8 {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure P]
    (μ : Measure 𝒵) [IsFiniteMeasure μ]
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ] (hκ : P.fst ⊗ₘ κ = P)
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (hR : risk P μ ℓ T' ≤ risk P μ ℓ (thresholdSet κ ℓ lam)) :
    expSize P μ (thresholdSet κ ℓ lam) ≤ expSize P μ T' := by sorry

end RiskControl.Optimal
