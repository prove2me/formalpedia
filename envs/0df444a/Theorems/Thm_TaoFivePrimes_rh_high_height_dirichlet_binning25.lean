-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning25
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning25
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:56:37.945987+00:00
-- url     : https://prove2.me/theorems/25e5acd7-c49d-4ae0-8b67-7fc296f7e588
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning25
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms38401 through39936. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues25
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins25

theorem TaoFivePrimes.rh_high_height_dirichlet_binning25 :
  RHHighDirichletBinning.bins RHHighDirichletValues25.rows.flatten=
    RHHighDirichletBins25.values.map RHHighDirichletBinning.decode := by sorry
