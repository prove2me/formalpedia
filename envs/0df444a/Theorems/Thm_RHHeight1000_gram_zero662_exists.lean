-- Prove2me | Theorems.Thm_RHHeight1000_gram_zero662_exists
-- name    : RHHeight1000.gram_zero662_exists
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T09:58:16.743882+00:00
-- url     : https://prove2.me/theorems/0d140835-11db-402b-8854-c1173de6307e
-- title:
--   A critical-line zero between 1017.79600 and 1019.02800
-- statement:
--   There exists a real number $t$ satisfying $$1017.79600<t<1019.02800,\qquad\zeta(\tfrac12+it)=0.$$ This interval supplies one critical-line zero for the finite Gram-block sequence used in the height-1000 counting certificate.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; Zeta.Certificates.Gram.z8_1_cert. Original complete AXLE certificate d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Mathlib

theorem RHHeight1000.gram_zero662_exists : ∃ t ∈ Set.Ioo (1017.79600 : ℝ) (1019.02800 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by sorry
