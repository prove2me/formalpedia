-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning03
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:56:07.373334+00:00
-- url     : https://prove2.me/theorems/709d71e3-92a0-4a55-828c-008de35cf1e5
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning03
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms4609 through6144. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues03
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins03

theorem TaoFivePrimes.rh_high_height_dirichlet_binning03 :
  RHHighDirichletBinning.bins RHHighDirichletValues03.rows.flatten=
    RHHighDirichletBins03.values.map RHHighDirichletBinning.decode := by sorry
