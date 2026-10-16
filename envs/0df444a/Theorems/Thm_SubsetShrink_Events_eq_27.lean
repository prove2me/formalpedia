-- Prove2me | Theorems.Thm_SubsetShrink_Events_eq_27
-- name    : SubsetShrink.Events.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:22.459837+00:00
-- url     : https://prove2.me/theorems/8f4331a0-06ce-4d47-a5f1-4da2695c7723
-- title:
--   (27), p. 38 — ‖Xu‖ ≤ ‖u‖₁ ≤ √s‖u‖ and √log(1/δ₀)‖Xu‖ ≤ √(s log(2ep/s))‖u‖ at δ₀ = s/(2ep)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $1\le s\le p$, and let $u\in\mathbb R^p$ satisfy $\|u\|_0\le s$. Then $\|Xu\|\le\|u\|_1\le\sqrt s\,\|u\|$, and with $\delta_0 = s/(2ep)$,
--   $$\sqrt{\log(1/\delta_0)}\,\|Xu\|\le\sqrt{s\log(2ep/s)}\,\|u\|.$$
--
--   This is the first step of the proof of Theorem 1 that reduces the event $\mathcal E_s$ to the event $\mathcal F$: at this value of $\delta_0$, the second entry of the maximum in $\mathcal F$ is dominated by the threshold of $\mathcal E_s$.
--
--   **Formalization Note** $\delta_0 = s/(2ep)$ is substituted directly, so $\log(1/\delta_0)$ appears as `Real.log (1 / (s / (2 * exp 1 * p)))`. Norms are the explicit Euclidean and $\ell_1$ norms on `Fin p → ℝ`.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 38, proof of Theorem 1 (B.1), (27) and the sentence before it

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem eq_27 {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (hs : 1 ≤ s) (hsp : s ≤ p) (u : Fin p → ℝ) (hu : l0 u ≤ s) :
    l2 (X.mulVec u) ≤ l1 u ∧ l1 u ≤ Real.sqrt s * l2 u ∧
      Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u) ≤
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by sorry
end SubsetShrink.Events
