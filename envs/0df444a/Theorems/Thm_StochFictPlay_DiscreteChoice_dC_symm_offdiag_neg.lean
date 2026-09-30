-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_dC_symm_offdiag_neg
-- name    : StochFictPlay.DiscreteChoice.dC_symm_offdiag_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:49:54.348986+00:00
-- url     : https://prove2.me/theorems/131ee9c1-3da9-4365-96a0-c0c91f7cc56b
-- title:
--   Eq. (4) — the derivative of the choice probability function is symmetric with strictly negative off-diagonal terms
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density $f$ on $\mathbb{R}^n$, and let $C : \mathbb{R}^n \to \mathbb{R}^n$ be the choice probability function $C_i(\pi) = P(\operatorname{argmax}_j \pi_j + \varepsilon_j = i)$ of the additive random utility model. Assume $C$ is continuously differentiable. Then for every payoff vector $\pi$ and every pair of distinct alternatives $i \neq j$,
--
--   $$
--   \frac{\partial C_i}{\partial \pi_j}(\pi) = \frac{\partial C_j}{\partial \pi_i}(\pi) \qquad\text{and}\qquad \frac{\partial C_i}{\partial \pi_j}(\pi) < 0 .
--   $$
--
--   So the derivative matrix $DC(\pi)$ is symmetric and its off-diagonal entries are strictly negative: raising the payoff of one alternative strictly lowers the probability of choosing any other.
--
--   Symmetry is what makes $C$ a gradient field, and the strict sign is what makes its potential strictly convex along the simplex; both are steps of the proof of Theorem 2.1.
--
--   **Formalization Note** $\partial C_i/\partial \pi_j(\pi)$ is the $i$-th component of the Fréchet derivative of $C$ at $\pi$ applied to the $j$-th unit vector. Alternatives are indexed by `Fin n`.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 6, eq. (4) and the two sentences after it

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

namespace StochFictPlay.DiscreteChoice

/-- Eq. (4) and the sentence after it (Hofbauer–Sandholm 2002, p. 6): for `i ≠ j`,
`∂Cᵢ/∂πⱼ(π) = ∂Cⱼ/∂πᵢ(π)` (the derivative matrix `DC(π)` is symmetric) and
`∂Cᵢ/∂πⱼ(π) < 0` (its off-diagonal terms are strictly negative). -/
theorem dC_symm_offdiag_neg {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) (π : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℝ (choiceProb f) π (Pi.single j 1) i = fderiv ℝ (choiceProb f) π (Pi.single i 1) j ∧
      fderiv ℝ (choiceProb f) π (Pi.single j 1) i < 0 := by sorry

end StochFictPlay.DiscreteChoice
