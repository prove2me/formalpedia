-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning23
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning23
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:44:00.93154+00:00
-- url     : https://prove2.me/theorems/33961d8d-929e-4b28-933c-90b0b4794012
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning23
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms35329 through36864. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues23
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins23

theorem TaoFivePrimes.rh_high_height_dirichlet_binning23 :
  RHHighDirichletBinning.bins RHHighDirichletValues23.rows.flatten=
    RHHighDirichletBins23.values.map RHHighDirichletBinning.decode := by sorry
