-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_weakLaw_shift
-- name    : RobustOdds.Tradeoff.weakLaw_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:14.564009+00:00
-- url     : https://prove2.me/theorems/cc71c7fb-0ab0-4be8-8aa1-36e97c8555bb
-- title:
--   App. C, p. 14 — subtracting 2ηy from each weak feature turns G_y into G_{−y}
-- statement:
--   Let $d \in \mathbb N$, $\eta \in \mathbb R$, and for $y \in \mathbb R$ let $G_y = \mathcal N(\eta y, 1)^{\otimes d}$ be the law of the weak features $(x_2, \dots, x_{d+1})$ in the data model (3). Let $T_y : \mathbb R^d \to \mathbb R^d$, $T_y(z)_i = z_i - 2\eta y$, subtract $2\eta y$ from every coordinate. Then for every $y \in \mathbb R$
--
--   $$ (T_y)_{\#}\, G_y = G_{-y}. $$
--
--   For $y = +1$ this says the adversary $x_i \mapsto x_i - \varepsilon y$ with $\varepsilon = 2\eta$ changes $G_+$ to $G_-$, and for $y = -1$ it changes $G_-$ to $G_+$. This is the mechanism behind Theorem 2.1: a perturbation of $\ell_\infty$ size $2\eta$ makes the weak features look as if they came from the other class.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 14, App. C, proof of Theorem 2.1, first paragraph

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- App. C, p. 14: the adversary that replaces `x_i` by `x_i − 2ηy` (`i ≥ 2`) maps the law of the
weak features under label `y` to their law under label `−y`; for `y = 1` it changes `G₊` to `G₋`,
for `y = −1` it changes `G₋` to `G₊`. -/
theorem weakLaw_shift (d : ℕ) (η : ℝ) :
    ∀ y : ℝ, (weakLaw d η y).map (fun z i => z i - 2 * η * y) = weakLaw d η (-y) := by sorry
end RobustOdds.Tradeoff
