-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_stdAcc_eq
-- name    : RobustOdds.Tradeoff.stdAcc_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:41.02821+00:00
-- url     : https://prove2.me/theorems/11d2f3bd-95a3-4731-ba16-28267a157b80
-- title:
--   App. C, p. 15 — standard accuracy = ½(p(1 + p₊₊ − p₋₋) + (1 − p)(1 + p₋₊ − p₊₋))
-- statement:
--   In the data model (3) with $\tfrac12 \le p \le 1$, let $f : \mathbb R^{d+1} \to \{-1, +1\}$ be a measurable classifier, and let $p_{ij}$ ($i, j \in \{+, -\}$) be the probability that $f$ predicts $+1$ when $x_1 = i$ (with $\pm$ read as $\pm 1$) and the weak features follow $G_j$. Then the standard accuracy of $f$ is
--
--   $$ \Pr_{(x,y)\sim\mathcal D}[f(x) = y] = \tfrac12\Big(p\,(1 + p_{++} - p_{--}) + (1-p)\,(1 + p_{-+} - p_{+-})\Big). $$
--
--   Conditioning on $y$ and on $x_1$ splits the accuracy into four cases, each a $p_{ij}$ or its complement. Together with the companion formula for the shift adversary, this turns Theorem 2.1 into an inequality between two linear expressions in the $p_{ij}$.
--
--   **Formalization Note** Measurability of $f$ and $f(x) \in \{\pm 1\}$ for every $x$ are the paper's "classifier that maps an input $x$ to a class in $\{-1,+1\}$"; they make $\Pr[f = -1] = 1 - \Pr[f = 1]$. The upper bound $p \le 1$ is part of $p$ being a probability.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 15, App. C, proof of Theorem 2.1, display for Pr(f(x) = y)

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- App. C, p. 15: the standard accuracy of a `{±1}`-valued classifier expressed in the `p_{ij}`. -/
theorem stdAcc_eq (d : ℕ) (p η : ℝ) (hp : 1 / 2 ≤ p) (hp1' : p ≤ 1)
    (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f) (hpm : ∀ x, f x = 1 ∨ f x = -1) :
    stdAcc d p η f = 1 / 2 * (p * (1 + pij d η f 1 1 - pij d η f (-1) (-1)) +
      (1 - p) * (1 + pij d η f (-1) 1 - pij d η f 1 (-1))) := by sorry
end RobustOdds.Tradeoff
