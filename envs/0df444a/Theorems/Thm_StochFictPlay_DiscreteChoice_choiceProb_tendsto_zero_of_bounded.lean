-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_choiceProb_tendsto_zero_of_bounded
-- name    : StochFictPlay.DiscreteChoice.choiceProb_tendsto_zero_of_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:21:20.670466+00:00
-- url     : https://prove2.me/theorems/e1eff8ab-6202-480b-8a88-fb51803d8bb4
-- title:
--   Range observation — bounded payoffs against payoffs tending to $+\infty$ have vanishing choice probabilities
-- statement:
--   Let $\varepsilon$ have a continuous, everywhere strictly positive density on $\mathbb{R}^n$ and let $C$ be the choice probability function of the additive random utility model. Let $J \subsetneq A$ be a proper subset of the alternatives, and let $(\pi^k)_{k \ge 0}$ be a sequence of payoff vectors such that
--
--   1. the components $\pi^k_j$, $j \in J$, stay bounded: $|\pi^k_j| \le B$ for all $k$ and all $j \in J$;
--   2. every remaining component tends to $+\infty$: $\pi^k_i \to +\infty$ as $k \to \infty$ for each $i \notin J$.
--
--   Then
--
--   $$
--   C_j(\pi^k) \longrightarrow 0 \qquad (k \to \infty) \quad \text{for all } j \in J .
--   $$
--
--   So $C(\pi^k)$ converges to the face of the simplex spanned by the alternatives outside $J$; in particular the range of $C$ contains points arbitrarily close to each corner of the simplex. This is what forces the range of $C$ to be the whole interior of the simplex in Theorem 2.1.
--
--   **Formalization Note** The paper states the observation for "components that approach infinity"; it is formalized with sequences, with $+\infty$ (which is what drives $C_j$ to $0$), and with $J$ proper (if $J = A$ the conclusion contradicts $\sum_j C_j = 1$). Differentiability of $C$ is not needed and not assumed.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 6, last paragraph (observation about the range of C)

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

open Filter Topology

namespace StochFictPlay.DiscreteChoice

/-- The range observation (Hofbauer–Sandholm 2002, p. 6): if the payoffs `πⱼ`, `j ∈ J`, stay
bounded while the remaining components tend to `+∞`, then `Cⱼ(π) → 0` for all `j ∈ J`. -/
theorem choiceProb_tendsto_zero_of_bounded {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (J : Finset (Fin n)) (hJ : Jᶜ.Nonempty)
    (π : ℕ → Fin n → ℝ) (hbdd : ∃ B : ℝ, ∀ k, ∀ j ∈ J, |π k j| ≤ B)
    (htop : ∀ i ∉ J, Tendsto (fun k => π k i) atTop atTop) :
    ∀ j ∈ J, Tendsto (fun k => choiceProb f (π k) j) atTop (𝓝 0) := by sorry

end StochFictPlay.DiscreteChoice
