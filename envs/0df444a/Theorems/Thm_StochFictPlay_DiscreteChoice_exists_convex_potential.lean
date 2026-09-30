-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_exists_convex_potential
-- name    : StochFictPlay.DiscreteChoice.exists_convex_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:29:33.206009+00:00
-- url     : https://prove2.me/theorems/bd79f014-e467-4208-a98c-9db910afd164
-- title:
--   The choice probability function is the gradient of a potential $W$ that is strictly convex on $\mathbb{R}^n_0$
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$, let $C$ be the choice probability function of the additive random utility model, and assume $C$ is continuously differentiable. Then there is a function $W : \mathbb{R}^n \to \mathbb{R}$ such that
--
--   1. $W$ is differentiable at every $\pi$ with $\nabla W \equiv C$, i.e. $\dfrac{\partial W}{\partial \pi_i}(\pi) = C_i(\pi)$ for all $\pi \in \mathbb{R}^n$ and $i \in A$;
--   2. $W$ is strictly convex on the tangent space $\mathbb{R}^n_0 = \{\pi : \sum_j \pi_j = 0\}$.
--
--   $$
--   \nabla W \equiv C, \qquad W|_{\mathbb{R}^n_0} \text{ strictly convex.}
--   $$
--
--   The potential is the expected maximal perturbed payoff $\mathbb{E}\max_j(\pi_j + \varepsilon_j)$ (McFadden 1981), up to an additive constant; its Legendre transform is the deterministic perturbation $V$ of Theorem 2.1.
--
--   **Formalization Note** $\partial W/\partial \pi_i(\pi)$ is the Fréchet derivative of $W$ at $\pi$ applied to the $i$-th unit vector. Strict convexity is Mathlib's `StrictConvexOn` on the subspace $\mathbb{R}^n_0$ viewed as a convex subset of `Fin n → ℝ`. $W$ is not strictly convex on all of $\mathbb{R}^n$, since it is affine along $\mathbf{1}$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 7, first paragraph

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex

namespace StochFictPlay.DiscreteChoice

/-- Hofbauer–Sandholm (2002), p. 7: the vector field `C` admits a potential function
`W : ℝⁿ → ℝ` with `∇W ≡ C`, and `W` is strictly convex on `R₀ⁿ`. -/
theorem exists_convex_potential {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) :
    ∃ W : (Fin n → ℝ) → ℝ,
      (∀ π : Fin n → ℝ, DifferentiableAt ℝ W π ∧
        ∀ i : Fin n, fderiv ℝ W π (Pi.single i 1) = choiceProb f π i) ∧
      StrictConvexOn ℝ (tangentSpace n : Set (Fin n → ℝ)) W := by sorry

end StochFictPlay.DiscreteChoice
