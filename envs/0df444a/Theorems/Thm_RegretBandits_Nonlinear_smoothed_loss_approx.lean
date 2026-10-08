-- Prove2me | Theorems.Thm_RegretBandits_Nonlinear_smoothed_loss_approx
-- name    : RegretBandits.Nonlinear.smoothed_loss_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:41:41.71539+00:00
-- url     : https://prove2.me/theorems/3b846a89-1f2b-47f6-9569-ce89d18a7915
-- title:
--   Eq. (6.2) — the smoothed loss is within δG of a G-Lipschitz loss
-- statement:
--   Let $d\ge1$, $\delta>0$, and let $\ell:\mathbb R^d\to\mathbb R$ be $G$-Lipschitz for the Euclidean norm. Let $\widetilde\ell(x)=\mathbb E\,\ell(x+\delta B)$ be its smoothed version, with $B$ uniform on the closed unit ball. Then for every $x\in\mathbb R^d$,
--   $$\big|\ell(x)-\widetilde\ell(x)\big|\le\delta G .$$
--
--   This bound converts regret against the smoothed losses into regret against the true losses at a cost of $\delta G$ per round.
--
--   **Formalization Note** The book derives (6.2) from the Lipschitz assumption alone, so convexity and differentiability are not assumed here.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 92, Eq. (6.2)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

open MeasureTheory
open scoped NNReal

namespace RegretBandits.Nonlinear

/-- Eq. (6.2) (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 92). If `ℓ : ℝ^d → ℝ` is
`G`-Lipschitz and `δ > 0`, then its smoothed version `ℓ̃(x) = E ℓ(x + δB)` (`B` uniform on the
closed unit ball) satisfies `|ℓ(x) - ℓ̃(x)| ≤ δG` for every `x ∈ ℝ^d`. -/
theorem smoothed_loss_approx {d : ℕ} (hd : 1 ≤ d) (G : ℝ≥0)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ) (hℓ : LipschitzWith G ℓ)
    (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    |ℓ x - smoothedLoss d δ ℓ x| ≤ δ * G := by sorry

end RegretBandits.Nonlinear
