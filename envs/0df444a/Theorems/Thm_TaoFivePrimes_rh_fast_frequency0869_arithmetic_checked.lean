-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_frequency0869_arithmetic_checked
-- name    : TaoFivePrimes.rh_fast_frequency0869_arithmetic_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:59:38.532122+00:00
-- url     : https://prove2.me/theorems/83e8afea-792a-4ec7-8f0c-853e7f21d7e1
-- title:
--   TaoFivePrimes.rh_fast_frequency0869_arithmetic_checked
-- statement:
--   The integer recurrence and5e-16 error-budget checker succeeds for24 proposed moment outputs at frequency869/512, using the published cached input balls and traces. Seed and polynomial accuracy, analytic interpretation and the full window are separate required proofs.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindowFrequency0869

theorem TaoFivePrimes.rh_fast_frequency0869_arithmetic_checked : RHFastBallFrequencyChecker.valid 869
 RHFastWindowFrequency0869.anchor RHFastWindowFrequency0869.pi RHFastWindowFrequency0869.root RHFastWindowFrequency0869.omega RHFastWindowFrequency0869.qs RHFastWindowFrequency0869.factors RHFastWindowFrequency0869.hs RHFastWindowFrequency0869.es RHFastWindowFrequency0869.ss RHFastWindowFrequency0869.reference=true := by sorry
