-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning31
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning31
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:32:52.096255+00:00
-- url     : https://prove2.me/theorems/eb6fe46c-7a38-4863-a9bc-f1c15d74a798
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning31
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms47617 through49152. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues31
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins31

theorem TaoFivePrimes.rh_high_height_dirichlet_binning31 :
  RHHighDirichletBinning.bins RHHighDirichletValues31.rows.flatten=
    RHHighDirichletBins31.values.map RHHighDirichletBinning.decode := by sorry
