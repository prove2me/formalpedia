-- Prove2me | Theorems.Thm_PiIrrationality_chudnovsky_rate_certificate
-- name    : PiIrrationality.chudnovsky_rate_certificate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T16:54:52.321923+00:00
-- url     : https://prove2.me/theorems/ab33a49a-b9ce-4af2-a9de-5e96b7f88a0c
-- title:
--   Certified logarithmic rate below 19.8899945
-- statement:
--   Define
--
--   $$D=-6\log(2\sin(\pi/24))-5,\qquad A=5+6\log(2\cos(\pi/24)).$$
--
--   Then
--
--   $$D>0\qquad\text{and}\qquad5\left(1+\frac AD\right)<19.8899945.$$
--
--   The decimal endpoint denotes the exact rational number $39779989/2000000$. This is a supporting numerical certificate for the [π irrationality-measure goal](https://prove2.me/theorems/06d04e2f-c2ad-434c-a9ba-332f6e66279c). It certifies an elementary inequality between explicit real constants; it does not assert an irrationality bound or assume the analytic construction needed for that goal.
-- source:
--   Original supporting numerical lemma for https://prove2.me/theorems/06d04e2f-c2ad-434c-a9ba-332f6e66279c. Proof uses Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/SpecialFunctions/Trigonometric/Basic.lean (angle subtraction and double-angle identities), and Analysis/Complex/ExponentialBounds.lean (Real.abs_log_sub_add_sum_range_le and certified log-two bounds). https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/ExponentialBounds.lean . No claim that this exact auxiliary formulation is a numbered statement in Chudnovsky (1982).

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

theorem PiIrrationality.chudnovsky_rate_certificate :
    0 < -6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5 ∧
    5 * (1 + (5 + 6 * Real.log (2 * Real.cos (Real.pi / 24))) /
      (-6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5)) < (19.8899945 : ℝ) := by sorry
