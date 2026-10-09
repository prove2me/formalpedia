-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_shiftAcc_eq
-- name    : RobustOdds.Tradeoff.shiftAcc_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:57.553508+00:00
-- url     : https://prove2.me/theorems/f0110f75-be05-492b-89c6-5200a2582849
-- title:
--   App. C, pp. 15–16 — accuracy against the shift adversary = ½(p(1 + p₊₋ − p₋₊) + (1 − p)(1 + p₋₋ − p₊₊))
-- statement:
--   In the data model (3) with $\tfrac12 \le p \le 1$, let $f : \mathbb R^{d+1} \to \{-1, +1\}$ be a measurable classifier, $p_{ij}$ as in the Setting file, and $x_{\mathrm{adv}}$ the input after the adversary replaces $x_i$ by $x_i - 2\eta y$ for each $i \ge 2$. Then
--
--   $$ \Pr_{(x,y)\sim\mathcal D}[f(x_{\mathrm{adv}}) = y] = \tfrac12\Big(p\,(1 + p_{+-} - p_{-+}) + (1-p)\,(1 + p_{--} - p_{++})\Big). $$
--
--   Since the adversary turns $G_+$ into $G_-$ and vice versa, the formula is that of the standard accuracy with the second index of every $p_{ij}$ flipped. It is the adversarial half of the reduction of Theorem 2.1 to an inequality in the $p_{ij}$.
--
--   **Formalization Note** As for the standard-accuracy formula: $f$ measurable and $\{\pm1\}$-valued, $p \le 1$.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, pp. 15–16, App. C, proof of Theorem 2.1, display for Pr(f(x_adv) = y)

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- App. C, pp. 15–16: the accuracy of a `{±1}`-valued classifier against the adversary that replaces
`G₊` with `G₋` (and vice-versa), expressed in the `p_{ij}`. -/
theorem shiftAcc_eq (d : ℕ) (p η : ℝ) (hp : 1 / 2 ≤ p) (hp1' : p ≤ 1)
    (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) (hpm : ∀ x, f x = 1 ∨ f x = -1) :
    shiftAcc d p η f = 1 / 2 * (p * (1 + pij d η f 1 (-1) - pij d η f (-1) 1) +
      (1 - p) * (1 + pij d η f (-1) (-1) - pij d η f 1 1)) := by sorry
end RobustOdds.Tradeoff
