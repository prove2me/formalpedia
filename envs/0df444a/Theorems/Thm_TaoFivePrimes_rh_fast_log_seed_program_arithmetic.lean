-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_log_seed_program_arithmetic
-- name    : TaoFivePrimes.rh_fast_log_seed_program_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:08:40.058389+00:00
-- url     : https://prove2.me/theorems/918f7670-8bc1-41e5-a9bc-0869d6ee1643
-- title:
--   TaoFivePrimes.rh_fast_log_seed_program_arithmetic
-- statement:
--   The two public integer logarithm programs at ratios2/1 and3289999936/2^31 equal the supplied cached balls. This independently checks their arithmetic; analytic logarithm containment requires the soundness theorem.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms

theorem TaoFivePrimes.rh_fast_log_seed_program_arithmetic :
 (RHFastBallSeedPrograms.logRatio 2 1,RHFastBallSeedPrograms.logRatio 3289999936 (2^31))=
 (⟨235865763225513294137944142764154484396,0,11⟩,⟨145161321996686247491177286792996021954,0,11⟩) := by sorry
