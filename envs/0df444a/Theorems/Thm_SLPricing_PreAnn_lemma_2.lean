-- Prove2me | Theorems.Thm_SLPricing_PreAnn_lemma_2
-- name    : SLPricing.PreAnn.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:49.215024+00:00
-- url     : https://prove2.me/theorems/5389c8b8-492d-4c49-a797-f9b1089c1be5
-- title:
--   Lemma 2, p. 13 — with social learning, the purchasing equilibrium is a threshold $[\theta,1]$, $\theta$ the unique solution of (3) in $[p_1,1]$ or $1$ under adoption inertia
-- statement:
--   Assume social learning is present, $\gamma>0$, and fix a pre-announced plan $\{p_1,p_2\}$ with $p_1\in[0,1]$. For $y\in[0,1]$ let $f(\cdot\,;y)$ be the pre-posterior law of $q_u$ when a mass $1-y$ of consumers buys early. Then:
--
--   1. a purchasing equilibrium exists;
--   2. if $p_1-\delta_c p_2\le 1-\delta_c$, the implicit equation
--   $$y-p_1=\delta_c\int_{p_2-y}^{\infty}(y+q_u-p_2)\,f(q_u;y)\,dq_u \tag{3}$$
--   has exactly one solution $y$ in $[p_1,1]$, and every purchasing equilibrium coincides with $[y,1]$ up to a null set;
--   3. if $p_1-\delta_c p_2>1-\delta_c$ (*adoption inertia*), every purchasing equilibrium is a null set: nobody buys in the first period.
--
--   The threshold $\theta(p_1,p_2)$ of the paper is $y$ in case 2 and $1$ in case 3. The left side of (3) is the marginal consumer's utility from buying now, the right side her expected utility from waiting for the reviews.
--
--   **Formalization Note** The integral in (3) is written as the expectation of $(y+q_u-p_2)^+$. The hypothesis $p_1\in[0,1]$ is added: for $p_1>1$ the interval $[p_1,1]$ is empty, and for $p_1<0$ the review mass $1-y$ would exceed $1$. Uniqueness of the equilibrium holds up to null sets, because the indifferent marginal type may go either way. Part (ii) of the lemma (second-period purchases iff $p_2-q_u\le x<\theta$) is built into the model's second-period demand and is not restated. The monotonicity clause is a separate item.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 2, (3), p. 13; proof, pp. 28–29

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Lemma 2, p. 13 (proof pp. 28–29): with social learning (`γ > 0`) and `p₁ ∈ [0, 1]`, a
purchasing equilibrium exists. If `p₁ − δc p₂ ≤ 1 − δc`, equation (3)
`y − p₁ = δc ∫ (y + q − p₂)⁺ f(q; y) dq` (`f(·; y)` the pre-posterior law for a mass `1 − y` of
reviews) has exactly one solution `y` in `[p₁, 1]`, and every equilibrium is `[y, 1]` up to a
null set. If `p₁ − δc p₂ > 1 − δc` (adoption inertia), every equilibrium is null. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (p₁ p₂ : ℝ)
    (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) :
    (∃ B : Set ℝ, IsPreEq P p₁ p₂ B) ∧
      (p₁ - P.δc * p₂ ≤ 1 - P.δc →
        ∃ y ∈ Icc p₁ 1,
          y - p₁ = P.δc * ∫ q, max (y + q - p₂) 0 ∂(prePost P (1 - y)) ∧
          (∀ y' ∈ Icc p₁ 1,
            y' - p₁ = P.δc * ∫ q, max (y' + q - p₂) 0 ∂(prePost P (1 - y')) → y' = y) ∧
          ∀ B : Set ℝ, IsPreEq P p₁ p₂ B → B =ᵐ[volume] Icc y 1) ∧
      (1 - P.δc < p₁ - P.δc * p₂ → ∀ B : Set ℝ, IsPreEq P p₁ p₂ B → volume B = 0) := by sorry

end SLPricing.PreAnn
