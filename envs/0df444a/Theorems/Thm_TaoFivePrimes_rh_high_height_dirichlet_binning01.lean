-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning01
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:46:17.99718+00:00
-- url     : https://prove2.me/theorems/5f838581-ad3c-4e0c-83ff-f2043bec7877
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning01
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms1537 through3072. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues01
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins01

theorem TaoFivePrimes.rh_high_height_dirichlet_binning01 :
  RHHighDirichletBinning.bins RHHighDirichletValues01.rows.flatten=
    RHHighDirichletBins01.values.map RHHighDirichletBinning.decode := by sorry
