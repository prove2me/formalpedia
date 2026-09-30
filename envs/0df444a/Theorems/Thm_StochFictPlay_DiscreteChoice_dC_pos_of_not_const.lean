-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_dC_pos_of_not_const
-- name    : StochFictPlay.DiscreteChoice.dC_pos_of_not_const
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:04:31.359918+00:00
-- url     : https://prove2.me/theorems/a631d6d9-69ea-4422-92ee-02c82dceaae3
-- title:
--   Eq. (6) — $z \cdot DC(\pi) z > 0$ for every $z$ not proportional to $\mathbf{1}$
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$, let $C$ be the choice probability function of the additive random utility model, and assume $C$ is continuously differentiable. For every payoff vector $\pi$ and every $z \in \mathbb{R}^n$ that is not proportional to the vector of ones $\mathbf{1}$,
--
--   $$
--   z \cdot DC(\pi)\, z = \sum_i \sum_j \frac{\partial C_i}{\partial \pi_j}(\pi)\, z_i z_j > 0 .
--   $$
--
--   In particular $DC(\pi)$ is positive definite on the tangent space $\mathbb{R}^n_0 = \{z : \sum_j z_j = 0\}$, since a nonzero vector of $\mathbb{R}^n_0$ is never proportional to $\mathbf{1}$.
--
--   This is the strict monotonicity of $C$ behind its injectivity on $\mathbb{R}^n_0$, the strict convexity of its potential, and the positive definiteness of $D^2V$ in Theorem 2.1.
--
--   **Formalization Note** "Not proportional to $\mathbf{1}$" is stated as: $z$ is not a constant vector. For $n = 1$ every vector is constant and the statement is vacuous.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 6, eq. (6)

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

namespace StochFictPlay.DiscreteChoice

/-- Eq. (6) (Hofbauer–Sandholm 2002, p. 6): if `z` is not proportional to the vector of ones,
then `z · DC(π) z > 0`. In particular `DC(π)` is positive definite on `R₀ⁿ`. -/
theorem dC_pos_of_not_const {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) (π z : Fin n → ℝ) (hz : ¬ ∃ c : ℝ, z = fun _ => c) :
    0 < z ⬝ᵥ fderiv ℝ (choiceProb f) π z := by sorry

end StochFictPlay.DiscreteChoice
