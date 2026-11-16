-- Prove2me | Theorems.Thm_PHIP1887_critical_coordinate
-- name    : PHIP1887.critical_coordinate
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:21:37.2402+00:00
-- url     : https://prove2.me/theorems/c4bdae1c-df60-4fc3-80f5-855214cc5be9
-- title:
--   A positive rational coordinate lies in the unit interval
-- statement:
--   Let $x$ and $b$ be positive real numbers. Then
--
--   $$0<\frac{x}{x+b}<1.$$
--
--   This elementary bound places the rational coordinate used in spectral atoms inside the real unit interval. Applying it to a spectral problem requires proving the positivity of its parameters separately.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PHIP-1887, declaration critical_coordinate in PHIP-1887_AXLE.lean; PF28 FINAL 15 November 2026, section 166.1. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9 . Elementary algebraic lemma; no novelty claim.

import Mathlib

theorem PHIP1887.critical_coordinate (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    0 < x/(x+b) ∧ x/(x+b) < 1 := by sorry
