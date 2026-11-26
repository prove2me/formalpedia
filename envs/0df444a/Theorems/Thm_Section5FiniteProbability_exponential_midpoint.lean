-- Prove2me | Theorems.Thm_Section5FiniteProbability_exponential_midpoint
-- name    : Section5FiniteProbability.exponential_midpoint
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:56.351566+00:00
-- url     : https://prove2.me/theorems/b11502c9-17dd-4781-9f6f-26c041138672
-- title:
--   Midpoint convexity of the real exponential
-- statement:
--   For every pair of real numbers a,b, $$\exp((a+b)/2)\le(\exp a+\exp b)/2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5FiniteCenteredExponential.lean, lines 31–32.

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory

theorem Section5FiniteProbability.exponential_midpoint (a b : ℝ) :
    Real.exp ((a+b)/2) ≤ (Real.exp a+Real.exp b)/2 := by sorry
