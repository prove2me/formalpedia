-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning26
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning26
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:00:17.285657+00:00
-- url     : https://prove2.me/theorems/56189b3d-f257-42ab-952b-494350e36dd8
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning26
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms39937 through41472. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues26
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins26

theorem TaoFivePrimes.rh_high_height_dirichlet_binning26 :
  RHHighDirichletBinning.bins RHHighDirichletValues26.rows.flatten=
    RHHighDirichletBins26.values.map RHHighDirichletBinning.decode := by sorry
