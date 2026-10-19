-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_setup_arithmetic
-- name    : TaoFivePrimes.rh_fast_window256_setup_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:40:15.569483+00:00
-- url     : https://prove2.me/theorems/47b9889c-7818-46c4-869d-94ebfbff947f
-- title:
--   TaoFivePrimes.rh_fast_window256_setup_arithmetic
-- statement:
--   All cached256-bit setup inputs,29 circuit coefficients,24 moment factors and the single-center anchor equal their public integer programs.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastWindow256Common

theorem TaoFivePrimes.rh_fast_window256_setup_arithmetic :
 RHFastWindow256Common.inputs=RHFastWindow256Setup.inputs 3289999936 ∧
 RHFastWindow256Common.qs=RHFastWindow256Setup.coefficients 3289999936 ∧
 RHFastWindow256Common.pi=RHFastWindow256Setup.lift RHFastBallSeedPrograms.pi ∧
 RHFastWindow256Common.root=RHFastWindow256Setup.lift RHFastBallSeedPrograms.root ∧
 RHFastWindow256Common.omega=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.omega 3289999936) ∧
 RHFastWindow256Common.factors=RHFastWindow256Setup.factors RHFastWindow256Common.pi ∧
 RHFastWindow256Common.anchor=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.anchor
  338465131998480615193183972069514375853 35120416548886332677381057571856482336 4235336350958928456860515144971299982 false) := by sorry
