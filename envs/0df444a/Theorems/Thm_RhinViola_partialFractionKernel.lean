-- Prove2me | Theorems.Thm_RhinViola_partialFractionKernel
-- name    : RhinViola.partialFractionKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T14:40:00.372748+00:00
-- url     : https://prove2.me/theorems/24dc527b-266a-4588-85d7-26853d9c4a94
-- title:
--   Partial-fraction identity for the Rhin-Viola monomial kernel
-- statement:
--   For h<m, the reciprocal product 1/((k+h+1)(k+m+1)) is the scaled difference of two reciprocal terms. This is the elementary partial-fraction identity that makes the off-diagonal Rhin-Viola monomial series telescope.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Tactic

theorem RhinViola.partialFractionKernel (h m k : ℕ) (hhm : h < m) :
    (1 : ℝ) /
        ((((k + h + 1 : ℕ) : ℝ)) * (((k + m + 1 : ℕ) : ℝ))) =
      (1 / ((m : ℝ) - (h : ℝ))) *
        ((1 / (((k + h + 1 : ℕ) : ℝ))) -
          (1 / (((k + m + 1 : ℕ) : ℝ)))) := by sorry
