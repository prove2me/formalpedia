-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_theorem_2_1
-- name    : RobustOdds.Tradeoff.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:09.854069+00:00
-- url     : https://prove2.me/theorems/85f62a6f-4e12-4431-9b85-77dfdc17d140
-- title:
--   Theorem 2.1, p. 5 — standard accuracy ≥ 1 − δ on D implies ℓ∞ robust accuracy ≤ (p/(1 − p))δ for ε ≥ 2η
-- statement:
--   **Theorem 2.1 (Robustness-accuracy trade-off).** Consider the data model (3): $y$ uniform on $\{-1,+1\}$; given $y$, $x_1 = +y$ with probability $p$ and $-y$ with probability $1-p$, and independently $x_2, \dots, x_{d+1}$ i.i.d. $\mathcal N(\eta y, 1)$, where $\tfrac12 \le p < 1$ and $\eta \ge 0$. Let $f : \mathbb R^{d+1} \to \{-1, +1\}$ be any measurable classifier and $\delta \in \mathbb R$. If
--
--   $$ \Pr_{(x,y)\sim\mathcal D}[f(x) = y] \ge 1 - \delta, $$
--
--   then for every $\varepsilon \ge 2\eta$
--
--   $$ \Pr_{(x,y)\sim\mathcal D}\big[f(x+\delta') = y \ \text{ for every } \delta' \text{ with } \|\delta'\|_\infty \le \varepsilon\big] \le \frac{p}{1-p}\,\delta. $$
--
--   Any classifier that attains at least $1 - \delta$ standard accuracy on $\mathcal D$ has robust accuracy at most $\frac{p}{1-p}\delta$ against an $\ell_\infty$-bounded adversary with $\varepsilon \ge 2\eta$. As standard accuracy approaches 100% ($\delta \to 0$), robust accuracy falls to 0, although the adversary's budget $2\eta$ is small compared with the scale $\pm1$ of the features: high standard accuracy forces reliance on the weakly correlated features, which the adversary can flip.
--
--   **Formalization Note** $\mathbb R^{d+1}$ is `Fin (d + 1) → ℝ` with the sup norm, so the ball is the $\ell_\infty$ ball. Four hypotheses are implicit on the page and stated here: $p < 1$ (the bound divides by $1-p$; in Lean $p/0 = 0$, and at $p = 1$ the classifier $\mathrm{sign}(x_1)$ would contradict the statement); $\eta \ge 0$ (the page takes $\eta$ "large enough", $\Theta(1/\sqrt d)$; for $\eta < 0$ and $\varepsilon = 0$ there is no adversary and the statement fails); measurability of $f$; and $f(x) \in \{\pm 1\}$ for every $x$. The robust event need not be measurable; its outer measure is used, i.e. its probability under the completion of $\mathcal D$.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 5, Theorem 2.1 (data model (3), p. 4; proof in App. C, pp. 14–16)

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 2.1 (Robustness-accuracy trade-off), p. 5: any classifier that attains at least `1 − δ`
standard accuracy on `D` has robust accuracy at most `(p/(1 − p))δ` against an `ℓ∞`-bounded adversary
with `ε ≥ 2η`. -/
theorem theorem_2_1 (d : ℕ) (p η ε δ : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1) (hη : 0 ≤ η)
    (hε : 2 * η ≤ ε) (f : (Fin (d + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hpm : ∀ x, f x = 1 ∨ f x = -1) (hacc : 1 - δ ≤ stdAcc d p η f) :
    robustAcc d p η f ε ≤ p / (1 - p) * δ := by sorry
end RobustOdds.Tradeoff
