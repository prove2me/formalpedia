-- Prove2me | Theorems.Thm_StaticCalendar_limit_term_increasing
-- name    : StaticCalendar.limit_term_increasing
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:15.148755+00:00
-- url     : https://prove2.me/theorems/0b2f0595-136c-4558-b056-b559b3244667
-- title:
--   p.ec15 — the limit term is increasing in $b$
-- statement:
--   The sequence $b\mapsto1-\frac{b^b}{b!}e^{-b}$ is strictly increasing on the positive integers, and at $b=1$ it equals $1-1/e$. This identifies $1-1/e$ as the worst case of the guarantee.
--
--   Differences from the source:
--   - reading: "increasing in $b$" → strictly increasing on $b\ge1$; reason: the usual meaning of "increasing", and true; the printed claim is implied
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, proof of Proposition EC.1, p.ec15

import Mathlib

namespace StaticCalendar

/-- arXiv:1811.01077v5, p.ec15: the term `1 - b^b e^{-b}/b!` "is increasing in `b`. So it obtains
minimum when `b = 1`", where it equals `1 - 1/e`. -/
theorem limit_term_increasing :
    StrictMonoOn (fun b : ℕ => 1 - (b : ℝ) ^ b * Real.exp (-(b : ℝ)) / (b.factorial : ℝ))
      (Set.Ici 1) ∧
    (1 : ℝ) - ((1 : ℕ) : ℝ) ^ 1 * Real.exp (-((1 : ℕ) : ℝ)) / ((1 : ℕ).factorial : ℝ) =
      1 - Real.exp (-1) := by sorry

end StaticCalendar
