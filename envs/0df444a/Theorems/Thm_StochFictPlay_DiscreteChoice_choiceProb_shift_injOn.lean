-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_choiceProb_shift_injOn
-- name    : StochFictPlay.DiscreteChoice.choiceProb_shift_injOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:12:49.751257+00:00
-- url     : https://prove2.me/theorems/e02f5b75-1748-4c34-8edd-d282f716376b
-- title:
--   Shift invariance $C(\pi + c\mathbf{1}) = C(\pi)$ and injectivity of $C$ on $\mathbb{R}^n_0$
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$, let $C$ be the choice probability function of the additive random utility model, and assume $C$ is continuously differentiable. Then
--
--   1. shifting payoffs by a constant vector does not affect choice probabilities: $C(\pi + c\mathbf{1}) = C(\pi)$ for all $\pi \in \mathbb{R}^n$ and $c \in \mathbb{R}$;
--   2. $C$ is one-to-one on the tangent space $\mathbb{R}^n_0 = \{\pi : \sum_j \pi_j = 0\}$: if $\pi, \pi' \in \mathbb{R}^n_0$ and $C(\pi) = C(\pi')$, then $\pi = \pi'$.
--
--   Together these say that choice probabilities determine payoffs up to a common additive constant, which is what allows $C$ restricted to $\mathbb{R}^n_0$ to be inverted in the Legendre-transform construction of Theorem 2.1.
--
--   **Formalization Note** $\pi + c\mathbf{1}$ is written `π + fun _ => c`.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 6, sentence after eq. (6)

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex

namespace StochFictPlay.DiscreteChoice

/-- Hofbauer–Sandholm (2002), p. 6: `C(π + c1) = C(π)` for all `c ∈ ℝ`, and `C` is
one-to-one on `R₀ⁿ`. -/
theorem choiceProb_shift_injOn {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) :
    (∀ (π : Fin n → ℝ) (c : ℝ), choiceProb f (π + fun _ => c) = choiceProb f π) ∧
      Set.InjOn (choiceProb f) (tangentSpace n : Set (Fin n → ℝ)) := by sorry

end StochFictPlay.DiscreteChoice
