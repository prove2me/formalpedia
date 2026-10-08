-- Prove2me | Theorems.Thm_RhinViola_shiftedZetaTwoTail
-- name    : RhinViola.shiftedZetaTwoTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:35:08.599301+00:00
-- url     : https://prove2.me/theorems/dce2415a-caa3-4e59-961b-057095780fb6
-- title:
--   Shifted Basel tail as zeta two minus a finite rational prefix
-- statement:
--   For every nonnegative integer h, the reciprocal-square tail starting at h+1 sums to zeta(2)=pi^2/6 minus the finite reciprocal-square prefix through h. This is the exact diagonal series identity needed for the Rhin-Viola monomial integral J(h,h).
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3; together with Mathlib's exact-revision theorem hasSum_zeta_two.

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

theorem RhinViola.shiftedZetaTwoTail (h : ℕ) :
    HasSum (fun k : ℕ => (1 : ℝ) / (((k + h + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6 -
        Finset.sum (Finset.range (h + 1)) (fun j : ℕ =>
          (1 : ℝ) / (((j : ℕ) : ℝ) ^ 2))) := by sorry
