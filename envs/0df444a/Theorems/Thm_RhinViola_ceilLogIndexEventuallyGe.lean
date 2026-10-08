-- Prove2me | Theorems.Thm_RhinViola_ceilLogIndexEventuallyGe
-- name    : RhinViola.ceilLogIndexEventuallyGe
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:39:24.047677+00:00
-- url     : https://prove2.me/theorems/7e0e6619-ca1b-406b-87c9-7b6c85e16459
-- title:
--   The Rhin–Viola ceiling index eventually exceeds any fixed threshold
-- statement:
--   For u>0 and any fixed natural threshold N, the index ceil(log(2q)/u) is at least N for every sufficiently large positive natural q. An explicit valid threshold is ceil(exp(uN)). This is the eventual-index step in Rhin–Viola Lemma 4.
-- source:
--   Elementary threshold step used in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem RhinViola.ceilLogIndexEventuallyGe
    (u : ℝ) (N : ℕ) (hu : 0 < u) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      N ≤ ⌈Real.log (2 * (q : ℝ)) / u⌉₊ := by sorry
