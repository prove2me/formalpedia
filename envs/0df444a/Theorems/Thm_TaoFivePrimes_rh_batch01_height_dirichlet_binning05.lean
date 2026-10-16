-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning05
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T16:42:37.289983+00:00
-- url     : https://prove2.me/theorems/f30536d9-0811-4298-8f19-3b65ef5e9a25
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning05
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms7681 through9216. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues05
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins05

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning05 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues05.rows.flatten=
    RHBatch01DirichletBins05.values.map RHHighDirichletBinning.decode := by sorry
