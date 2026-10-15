-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning15
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning15
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:02:47.734523+00:00
-- url     : https://prove2.me/theorems/623873fb-965f-4b3d-8e91-2fc279637712
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning15
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms23041 through24576. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues15
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins15

theorem TaoFivePrimes.rh_high_height_dirichlet_binning15 :
  RHHighDirichletBinning.bins RHHighDirichletValues15.rows.flatten=
    RHHighDirichletBins15.values.map RHHighDirichletBinning.decode := by sorry
