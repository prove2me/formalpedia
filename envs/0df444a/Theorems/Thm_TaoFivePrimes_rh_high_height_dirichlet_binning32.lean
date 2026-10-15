-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning32
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning32
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:36:15.321513+00:00
-- url     : https://prove2.me/theorems/7eb0b751-092c-4b01-8a2c-80faabd918c4
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning32
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms49153 through50000. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues32
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins32

theorem TaoFivePrimes.rh_high_height_dirichlet_binning32 :
  RHHighDirichletBinning.bins RHHighDirichletValues32.rows.flatten=
    RHHighDirichletBins32.values.map RHHighDirichletBinning.decode := by sorry
