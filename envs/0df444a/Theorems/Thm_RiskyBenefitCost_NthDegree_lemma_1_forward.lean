-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_lemma_1_forward
-- name    : RiskyBenefitCost.NthDegree.lemma_1_forward
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:19.696791+00:00
-- url     : https://prove2.me/theorems/4245446a-fd6c-4751-8daa-7053378e17f4
-- title:
--   Lemma 1 (Ekern 1980), (i) ⇒ (ii), p. 3626 (PDF 3) — an Nth-degree risk increase lowers expected utility for every Nth-degree risk averter
-- statement:
--   Let $N\ge1$ and $\underline x<\bar x$. Let $\tilde X_1,\tilde X_2$ be random variables with values in $[\underline x,\bar x]$, with laws $\mu_1,\mu_2$ and distribution functions $F,G$, and suppose $\tilde X_2$ is an $N$th-degree risk increase over $\tilde X_1$ in the sense of Ekern: $F^{(k)}(\bar x)=G^{(k)}(\bar x)$ for $k=1,\dots,N$ and $F^{(N)}\le G^{(N)}$ on $[\underline x,\bar x]$.
--
--   Then for every $N$ times continuously differentiable function $u:\mathbb R\to\mathbb R$ with $(-1)^{N+1}u^{(N)}(z)\ge 0$ for all $z\in[\underline x,\bar x]$,
--   $$\mathbb E\,u(\tilde X_2)\le \mathbb E\,u(\tilde X_1).$$
--
--   This is the direction (i) $\Rightarrow$ (ii) of Ekern's characterization: an $N$th-degree risk increase makes every $N$th-degree risk averter worse off. It is the tool that turns the distributional condition of Definition 2 into a comparison of expected utilities, and so into increasing differences of the objective in Lemma 3.
--
--   **Formalization Note.** Only the direction (i) $\Rightarrow$ (ii) of the paper's equivalence is stated. The page's "any function $U(z)$" is read as $u\in C^N(\mathbb R)$, the smoothness the integration-by-parts argument needs; the sign condition is required only on $[\underline x,\bar x]$, where the laws live, which is no weaker than the page. Random variables are represented by their laws, probability measures on $\mathbb R$ giving zero mass to the complement of $[\underline x,\bar x]$.
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3626 (PDF 3), Lemma 1 (direction i ⇒ ii)

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree
open MeasureTheory ProbabilityTheory

theorem lemma_1_forward (N : ℕ) (hN : 1 ≤ N) (xl xu : ℝ) (hlt : xl < xu)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : μ₁ (Set.Icc xl xu)ᶜ = 0) (hμ₂ : μ₂ (Set.Icc xl xu)ᶜ = 0)
    (hinc : IsNthDegreeRiskIncrease N xl xu μ₁ μ₂)
    (u : ℝ → ℝ) (hu : ContDiff ℝ N u) (hsign : NthDegreeRiskAverseOn N u (Set.Icc xl xu)) :
    ∫ x, u x ∂μ₂ ≤ ∫ x, u x ∂μ₁ := by sorry

end RiskyBenefitCost.NthDegree
