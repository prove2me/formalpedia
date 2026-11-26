-- Prove2me | Theorems.Thm_RHHeight1000_gram_zero664_exists
-- name    : RHHeight1000.gram_zero664_exists
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T09:58:27.43852+00:00
-- url     : https://prove2.me/theorems/5c51d3cc-39b4-4e8d-9e1a-491db2131ba3
-- title:
--   A critical-line zero between 1020.26600 and 1021.49700
-- statement:
--   There exists a real number $t$ satisfying $$1020.26600<t<1021.49700,\qquad\zeta(\tfrac12+it)=0.$$ This interval supplies one critical-line zero for the finite Gram-block sequence used in the height-1000 counting certificate.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; Zeta.Certificates.Gram.z10_1_cert. Original complete AXLE certificate d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Mathlib

theorem RHHeight1000.gram_zero664_exists : ∃ t ∈ Set.Ioo (1020.26600 : ℝ) (1021.49700 : ℝ), riemannZeta (1 / 2 + Complex.I * t) = 0 := by sorry
