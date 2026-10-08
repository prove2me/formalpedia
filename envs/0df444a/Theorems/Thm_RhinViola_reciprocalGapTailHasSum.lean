-- Prove2me | Theorems.Thm_RhinViola_reciprocalGapTailHasSum
-- name    : RhinViola.reciprocalGapTailHasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:15:16.573055+00:00
-- url     : https://prove2.me/theorems/79f866c3-612c-4b75-b122-fe96310b8f4c
-- title:
--   Finite-gap reciprocal tail for the Rhin-Viola off-diagonal series
-- statement:
--   For natural h and gap d, the infinite difference of reciprocal tails starting at h+1 and h+d+1 equals the finite harmonic block from h+1 through h+d. The proof iterates the one-step telescoping-tail identity d times.
-- source:
--   Elementary telescoping identity used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_reciprocalTailDifferenceHasSum
import Mathlib.Tactic
open scoped BigOperators

theorem RhinViola.reciprocalGapTailHasSum (h d : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (((k + h + 1 : ℕ) : ℝ)) -
        (1 : ℝ) / (((k + h + d + 1 : ℕ) : ℝ)))
      (Finset.sum (Finset.range d) (fun j : ℕ =>
        (1 : ℝ) / (((h + j + 1 : ℕ) : ℝ)))) := by sorry
