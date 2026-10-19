-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_arithmetic
-- name    : TaoFivePrimes.rh_batch01_new256_setup_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:22:12.434002+00:00
-- url     : https://prove2.me/theorems/18d03ab0-f513-4cb5-9155-a01f27d738d5
-- title:
--   TaoFivePrimes.rh_batch01_new256_setup_arithmetic
-- statement:
--   Ordinary kernel evaluation checks the fresh center anchor and all cached setup programs.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original mathematical attribution: sometik179, submission c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHBatch01New256Common
open RHFastBallArithmetic

theorem TaoFivePrimes.rh_batch01_new256_setup_arithmetic :
 RHBatch01New256Common.inputs=RHFastWindow256Setup.inputs 3289999808 ∧
 RHBatch01New256Common.qs=RHFastWindow256Setup.coefficients 3289999808 ∧
 RHBatch01New256Common.pi=RHFastWindow256Setup.lift RHFastBallSeedPrograms.pi ∧
 RHBatch01New256Common.root=RHFastWindow256Setup.lift RHFastBallSeedPrograms.root ∧
 RHBatch01New256Common.omega=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.omega 3289999808) ∧
 RHBatch01New256Common.factors=RHFastWindow256Setup.factors RHBatch01New256Common.pi ∧
 RHBatch01New256Common.anchor=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.anchor
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).cos
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).sin
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).amplitude
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).negative) := by sorry
