-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_dC_diag_and_mulVec_one
-- name    : StochFictPlay.DiscreteChoice.dC_diag_and_mulVec_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:57:30.467975+00:00
-- url     : https://prove2.me/theorems/ed44ac17-72e3-4634-987f-102ede364fb9
-- title:
--   Eq. (5) and $DC(\pi)\mathbf{1} = 0$ — diagonal terms of the derivative of the choice probability function
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$, let $C$ be the choice probability function of the additive random utility model, and assume $C$ is continuously differentiable. For every payoff vector $\pi$ and every alternative $i$,
--
--   $$
--   \frac{\partial C_i}{\partial \pi_i}(\pi) = -\sum_{j \neq i} \frac{\partial C_j}{\partial \pi_i}(\pi),
--   $$
--
--   and $DC(\pi)\,\mathbf{1} = 0$, where $\mathbf{1} \in \mathbb{R}^n$ is the vector of ones.
--
--   The first identity is the derivative of $\sum_j C_j(\pi) = 1$; the second says that shifting all payoffs by the same amount does not change choice probabilities to first order. Together with the symmetry of $DC(\pi)$ they reduce the quadratic form of $DC(\pi)$ to its off-diagonal terms.
--
--   **Formalization Note** $\partial C_j/\partial \pi_i(\pi)$ is the $j$-th component of the Fréchet derivative of $C$ at $\pi$ applied to the $i$-th unit vector, and $DC(\pi)\mathbf{1}$ is that derivative applied to the constant vector with entries $1$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 6, eq. (5) and the sentence after it

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

namespace StochFictPlay.DiscreteChoice

/-- Eq. (5) and `DC(π) 1 = 0` (Hofbauer–Sandholm 2002, p. 6):
`∂Cᵢ/∂πᵢ(π) = -∑_{j ≠ i} ∂Cⱼ/∂πᵢ(π)` for every `i`, and the derivative `DC(π)` maps the
vector of ones to zero. -/
theorem dC_diag_and_mulVec_one {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) (π : Fin n → ℝ) :
    (∀ i : Fin n, fderiv ℝ (choiceProb f) π (Pi.single i 1) i =
        -∑ j ∈ Finset.univ.erase i, fderiv ℝ (choiceProb f) π (Pi.single i 1) j) ∧
      fderiv ℝ (choiceProb f) π (fun _ => 1) = 0 := by sorry

end StochFictPlay.DiscreteChoice
