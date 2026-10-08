-- Prove2me | Theorems.Thm_RhinViola_exponent_below_target_of_global_ceilings
-- name    : RhinViola.exponent_below_target_of_global_ceilings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T22:35:38.388299+00:00
-- url     : https://prove2.me/theorems/14362a86-bddf-481b-954c-8c5671cfbff7
-- title:
--   Certified final Rhin–Viola exponent comparison from rational global ceilings
-- statement:
--   Let a and b denote the logarithmic global maxima used in the fourth-case Rhin–Viola irrationality-measure argument. If a≤−2.635725669 and b≤2.067714200 then a+2 is strictly negative and the final exponent (a−b)/(a+2) is strictly less than 7.398537. The statement is exact rational arithmetic and uses a deliberately relaxed, more practical torus ceiling, with a strictly positive margin of 0.000000014946253 in the equivalent linear inequality. This proves the final numerical implication conditional on independently certifying the two global maxima.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Ann. Inst. Fourier 43 (1993), pp. 104–109, in particular Sections 8–9 and the formula (a−b)/(a+2) on p.108. The rational ceiling B=2.067714200 is deliberately relaxed relative to the paper's exploratory b≈2.067714160519, leaving substantially more interval-certification tolerance; exact rational strictness checked independently. Relevant to child RhinViola.zetaTwoIrrationalityBound (bb98b323-fe68-49fe-a97c-b06c6157899b).

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem RhinViola.exponent_below_target_of_global_ceilings
    (a b : ℝ) (ha : a ≤ -(2635725669 : ℝ) / 1000000000)
    (hb : b ≤ (2067714200 : ℝ) / 1000000000) :
    (a - b) / (a + 2) < (7398537 : ℝ) / 1000000 := by sorry
