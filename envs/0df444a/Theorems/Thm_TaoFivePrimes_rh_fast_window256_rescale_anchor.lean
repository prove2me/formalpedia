-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_rescale_anchor
-- name    : TaoFivePrimes.rh_fast_window256_rescale_anchor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:44:04.968557+00:00
-- url     : https://prove2.me/theorems/8e24666c-ab44-4abe-908c-8ab59f7be0e7
-- title:
--   TaoFivePrimes.rh_fast_window256_rescale_anchor
-- statement:
--   Exact integer rescaling preserves128-bit ball containment at256 bits, and the independently checked single-center seed program encloses the exact polynomial anchor.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
open Complex

theorem TaoFivePrimes.rh_fast_window256_rescale_anchor :
 (∀(a:RHFastBallArithmetic.Ball)(z:ℂ),RHFastBallSemantics.encloses RHFastBallSeedPrograms.D a z →
  RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastWindow256Setup.lift a) z) ∧
 RHFastBallSemantics.encloses RHFastBallSeedPrograms.D
  (RHFastBallSeedPrograms.anchor 338465131998480615193183972069514375853 35120416548886332677381057571856482336 4235336350958928456860515144971299982 false)
  (RHFastGaussianWindow.anchor 3289999936) := by sorry
