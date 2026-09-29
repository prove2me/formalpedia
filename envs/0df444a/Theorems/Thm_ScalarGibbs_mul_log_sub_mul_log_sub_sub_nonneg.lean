-- Prove2me | Theorems.Thm_ScalarGibbs_mul_log_sub_mul_log_sub_sub_nonneg
-- name    : ScalarGibbs.mul_log_sub_mul_log_sub_sub_nonneg
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T03:24:14.972292+00:00
-- url     : https://prove2.me/theorems/c2c82425-47d9-43b0-a1ea-60fb91ccb676
-- title:
--   Scalar Gibbs inequality: $y\log(y/u)\ge y-u$
-- statement:
--   **Scalar Gibbs / Bregman inequality for $t\log t$.** For $y \ge 0$ and $u > 0$, $y\log y - y\log u - (y-u) \ge 0$ (equivalently $y\log(y/u) \ge y - u$). This is the pointwise variational ingredient behind the variational formula of entropy (Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, Theorem 4.13) and its use in the modified logarithmic Sobolev inequality (Theorem 6.6): applied conditionally with $y = e^{\lambda Z}$, $u = e^{\lambda Z_i}$ it produces the per-coordinate summand $e^{\lambda Z}\varphi(-\lambda(Z-Z_i))$ with $\varphi(x) = e^x - x - 1$.
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities (OUP 2013), Theorem 4.13 (variational formula of entropy) and Theorem 6.6 (modified logarithmic Sobolev inequality), Section 6.3.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
open Real

theorem ScalarGibbs.mul_log_sub_mul_log_sub_sub_nonneg {y u : ℝ} (hy : 0 ≤ y) (hu : 0 < u) :
    0 ≤ y * Real.log y - y * Real.log u - (y - u) := by sorry
