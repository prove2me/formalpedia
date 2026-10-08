-- Prove2me | Theorems.Thm_RhinViola_normalizedLogLimitToExponentialBounds
-- name    : RhinViola.normalizedLogLimitToExponentialBounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-05T23:34:34.837579+00:00
-- url     : https://prove2.me/theorems/bf09d35c-5f87-432a-afb1-bac0ab04c18e
-- title:
--   Convert the normalized logarithmic linear-form limit to eventual exponential bounds
-- statement:
--   If log|f_n|/n tends to -sigma and f_n is eventually nonzero, then for every positive delta the sequence is eventually trapped between exp(-(sigma+delta)n) and exp(-(sigma-delta)n). This is the direct asymptotic-to-explicit wrapper for the linear forms in Rhin-Viola Lemma 4.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Lemma 4.

import Theorems.Thm_RhinViola_normalizedLogLimitEventuallyBand
import Theorems.Thm_RhinViola_normalizedLogBoundsToExponentialBounds
import Mathlib.Tactic

theorem RhinViola.normalizedLogLimitToExponentialBounds
    (sigma : Real) (f : Nat -> Real)
    (hlim : Filter.Tendsto (fun n : Nat => Real.log |f n| / (n : Real)) Filter.atTop (nhds (-sigma)))
    (hnz : exists N0 : Nat, forall n : Nat, N0 <= n -> f n != 0) :
    forall delta : Real, 0 < delta ->
      exists N : Nat, forall n : Nat, N <= n ->
        Real.exp (-((sigma + delta) * (n : Real))) <= |f n| /\
        |f n| <= Real.exp (-((sigma - delta) * (n : Real))) := by sorry
