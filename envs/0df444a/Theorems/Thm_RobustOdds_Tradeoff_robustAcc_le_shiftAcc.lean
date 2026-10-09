-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_robustAcc_le_shiftAcc
-- name    : RobustOdds.Tradeoff.robustAcc_le_shiftAcc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:30.00356+00:00
-- url     : https://prove2.me/theorems/667a1b3e-abab-46fb-8883-d1d740b8fdc6
-- title:
--   App. C, p. 14 — for ε ≥ 2η ≥ 0, ℓ∞ robust accuracy ≤ accuracy against the fixed shift adversary
-- statement:
--   In the data model (3) with parameters $d, p, \eta$, let $f : \mathbb R^{d+1} \to \mathbb R$ be any function. Let $\mathrm{acc}_\varepsilon(f)$ be its $\ell_\infty$ robust accuracy at radius $\varepsilon$ and $\mathrm{acc}_{\mathrm{adv}}(f)$ its accuracy against the fixed adversary that replaces $x_i$ by $x_i - 2\eta y$ for each $i \ge 2$ (both defined in the Setting file). If $0 \le \eta$ and $2\eta \le \varepsilon$, then
--
--   $$ \mathrm{acc}_\varepsilon(f) \le \mathrm{acc}_{\mathrm{adv}}(f). $$
--
--   The fixed perturbation has $\ell_\infty$ norm $2\eta$ (or $0$ when $d = 0$), so it is one of the perturbations the worst-case adversary may choose. This is the step "fix the adversary" of the proof of Theorem 2.1, which reduces the worst case over the ball to one explicit adversary.
--
--   **Formalization Note** No measurability of $f$ is needed: the robust event is contained in the event that $f$ is correct on the shifted input, and the measure applied to the robust event is its outer measure.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 14, App. C, proof of Theorem 2.1 ("fix the adversary that replaces x_i by x_i − yε")

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- App. C, p. 14: for `ε ≥ 2η ≥ 0` the fixed adversary `shiftAdv` lies in the `ℓ∞` ball of radius `ε`,
so `ℓ∞`-robust accuracy is at most the accuracy against that adversary. -/
theorem robustAcc_le_shiftAcc (d : ℕ) (p η ε : ℝ) (hη : 0 ≤ η) (hε : 2 * η ≤ ε)
    (f : (Fin (d + 1) → ℝ) → ℝ) :
    robustAcc d p η f ε ≤ shiftAcc d p η f := by sorry
end RobustOdds.Tradeoff
