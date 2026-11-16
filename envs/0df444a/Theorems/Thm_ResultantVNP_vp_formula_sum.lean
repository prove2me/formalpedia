-- Prove2me | Theorems.Thm_ResultantVNP_vp_formula_sum
-- name    : ResultantVNP.vp_formula_sum
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T21:25:38.08195+00:00
-- url     : https://prove2.me/theorems/b8888d04-6207-47b2-9c8d-0e2edf8b7026
-- title:
--   Polynomial-size Boolean sums of formulas simulate VP
-- statement:
--   Every family in VP over the complex numbers can be written as a Boolean sum of a polynomial-size arithmetic-formula family. The number of Boolean witness variables and formula gate count are polynomially bounded. The underlying VP definition counts only arithmetic gates, permits arbitrary complex constants, and bounds the actual output degree; intermediate cancellations are allowed.
-- source:
--   Valiant, Completeness classes in algebra, STOC 1979; see also Hrubeš, Wigderson and Yehudayoff, Relationless completeness and separations, Theorem 11 and Section IV-A, https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HWY10_rel/HWY10_rel_proc.pdf.

import Definitions.Def_ResultantVNP_FormulaWitness

theorem ResultantVNP.vp_formula_sum : VNPNestedBooleanSum.VPFormulaSumProperty := by sorry
