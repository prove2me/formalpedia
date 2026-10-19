-- Prove2me | Theorems.Thm_PeriodicDividend_FixedPoint_theorem_3_3_D
-- name    : PeriodicDividend.FixedPoint.theorem_3_3_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:04.763386+00:00
-- url     : https://prove2.me/theorems/e750889d-24e1-4845-a9a8-31c80d03e015
-- title:
--   Theorem 3.3, p. 6 — D maps Ĉ_A into C_A
-- statement:
--   For every $A\ge0$, the dividend operator maps the larger continuation class $\widehat{\mathcal C}_A$ into $\mathcal C_A$:
--
--   $$\phi\in\widehat{\mathcal C}_A\quad\Longrightarrow\quad\mathcal D\phi\in\mathcal C_A.$$
--
--   In particular, optimizing the dividend at a payment date preserves the class needed for the one-period fixed-point operator.
-- source:
--   Keppo, Reppen, Soner, Discrete dividend payments in continuous time, arXiv:1805.05077v2, p. 6, Theorem 3.3, first sentence

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicDividend.FixedPoint

/-- First assertion of Theorem 3.3: dividend optimization maps Ĉ_A into C_A. -/
theorem theorem_3_3_D (p : Params) (hS : p.Standing) (A : ℝ) (hA : 0 ≤ A)
    (φ : ℝ≥0 → ℝ) (hφ : ChatA p A φ) : CA p A (Dop φ) := by sorry

end PeriodicDividend.FixedPoint
