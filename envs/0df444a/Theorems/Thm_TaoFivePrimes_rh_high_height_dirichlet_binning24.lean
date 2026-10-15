-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning24
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning24
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:49:14.983706+00:00
-- url     : https://prove2.me/theorems/1387f9c6-4b6f-4040-900b-e9a506a54c3f
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning24
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms36865 through38400. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues24
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins24

theorem TaoFivePrimes.rh_high_height_dirichlet_binning24 :
  RHHighDirichletBinning.bins RHHighDirichletValues24.rows.flatten=
    RHHighDirichletBins24.values.map RHHighDirichletBinning.decode := by sorry
