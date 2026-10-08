-- Prove2me | Theorems.Thm_RhinViola_coefficientNonzeroOfSmallLinearForm
-- name    : RhinViola.coefficientNonzeroOfSmallLinearForm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:24:22.750407+00:00
-- url     : https://prove2.me/theorems/d76ef763-1e04-4ee1-b8bb-1bb1bb123ca4
-- title:
--   A small nonzero integer linear form has nonzero coefficient
-- statement:
--   If f=a-bα is nonzero and |f|<1 with integer a and b, then b is nonzero. Indeed, b=0 would make f=a a nonzero integer, whose absolute value is at least 1. This is the eventual b_n≠0 step in Rhin and Viola's Lemma 4.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

theorem RhinViola.coefficientNonzeroOfSmallLinearForm
    (α f : ℝ) (a b : ℤ)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hfnz : f ≠ 0) (hsmall : |f| < 1) :
    b ≠ 0 := by sorry
