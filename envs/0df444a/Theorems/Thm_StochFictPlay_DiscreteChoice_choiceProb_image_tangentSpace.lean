-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_choiceProb_image_tangentSpace
-- name    : StochFictPlay.DiscreteChoice.choiceProb_image_tangentSpace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:36:59.454974+00:00
-- url     : https://prove2.me/theorems/9e9def32-c43c-41a0-bb0b-d5b109ff7a56
-- title:
--   The range of $C$ on $\mathbb{R}^n_0$ is all of $\operatorname{int}(\Delta A)$
-- statement:
--   Let $n \ge 1$, let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$, let $C$ be the choice probability function of the additive random utility model, and assume $C$ is continuously differentiable. Then $C(\pi) \in \operatorname{int}(\Delta A)$ for every payoff vector $\pi \in \mathbb{R}^n$, and
--
--   $$
--   C(\mathbb{R}^n_0) = \operatorname{int}(\Delta A),
--   $$
--
--   where $\mathbb{R}^n_0 = \{\pi : \sum_j \pi_j = 0\}$ and $\operatorname{int}(\Delta A) = \{y : y_i > 0 \text{ for all } i,\ \sum_i y_i = 1\}$.
--
--   Every interior mixed choice is therefore the choice probability vector of some normalized payoff vector (exactly one, by injectivity on $\mathbb{R}^n_0$); this is the statement that the Legendre transform $V$ of Theorem 2.1 is defined on the whole interior of the simplex.
--
--   **Formalization Note** The paper obtains the range statement from Theorem 26.5 of Rockafellar (1970); it is stated here in the paper's own terms. The first conjunct ($C$ takes values in the open simplex) is used on p. 7, where $C$ is written as a map $\mathbb{R}^n_0 \to \operatorname{int}(\Delta A)$. For $n = 0$ the open simplex is empty, hence the hypothesis $n \ge 1$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 7, second paragraph (the domain of V equals the range of C, which must be all of int(ΔA))

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex

namespace StochFictPlay.DiscreteChoice

/-- Hofbauer–Sandholm (2002), p. 7: `C` takes values in `int(ΔA)`, and the range of `C` on
`R₀ⁿ` is all of `int(ΔA)`. -/
theorem choiceProb_image_tangentSpace {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (hC : ContDiff ℝ 1 (choiceProb f)) :
    (∀ π : Fin n → ℝ, choiceProb f π ∈ openSimplex n) ∧
      choiceProb f '' (tangentSpace n : Set (Fin n → ℝ)) = openSimplex n := by sorry

end StochFictPlay.DiscreteChoice
