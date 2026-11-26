-- Prove2me | Theorems.Thm_RHHeight1000_gram_zero663_exists
-- name    : RHHeight1000.gram_zero663_exists
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T09:58:24.038463+00:00
-- url     : https://prove2.me/theorems/a59c3c6e-f5ce-47be-b389-ce1aff343f75
-- title:
--   A critical-line zero between 1019.03100 and 1020.26300
-- statement:
--   There exists a real number $t$ satisfying $$1019.03100<t<1020.26300,\qquad\zeta(\tfrac12+it)=0.$$ This interval supplies one critical-line zero for the finite Gram-block sequence used in the height-1000 counting certificate.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; Zeta.Certificates.Gram.z9_1_cert. Original complete AXLE certificate d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Mathlib

theorem RHHeight1000.gram_zero663_exists : ∃ t ∈ Set.Ioo (1019.03100 : ℝ) (1020.26300 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by sorry
