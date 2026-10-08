-- Prove2me | Theorems.Thm_RhinViola_normalizedLogCoefficientLimitToExponentialBound
-- name    : RhinViola.normalizedLogCoefficientLimitToExponentialBound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-05T23:34:41.789653+00:00
-- url     : https://prove2.me/theorems/20107458-f7db-4d70-8caa-83fd255e146d
-- title:
--   Convert a normalized logarithmic coefficient limit to an eventual exponential bound
-- statement:
--   If log|b_n|/n tends to rho, then for every positive delta the integer coefficient sequence is eventually bounded by exp((rho+delta)n). This is a stronger-limit version of the coefficient-growth hypothesis used in Rhin-Viola Lemma 4 and isolates the conversion to explicit estimates.
-- source:
--   Asymptotic wrapper for G. Rhin and C. Viola, On the irrationality measure of zeta(2), Lemma 4.

import Theorems.Thm_RhinViola_normalizedLogLimitEventuallyBand
import Theorems.Thm_RhinViola_normalizedLogCoefficientBoundToExponential
import Mathlib.Tactic

theorem RhinViola.normalizedLogCoefficientLimitToExponentialBound
    (rho : Real) (b : Nat -> Int)
    (hlim : Filter.Tendsto (fun n : Nat => Real.log |(b n : Real)| / (n : Real)) Filter.atTop (nhds rho)) :
    forall delta : Real, 0 < delta ->
      exists N : Nat, forall n : Nat, N <= n ->
        |(b n : Real)| <= Real.exp ((rho + delta) * (n : Real)) := by sorry
