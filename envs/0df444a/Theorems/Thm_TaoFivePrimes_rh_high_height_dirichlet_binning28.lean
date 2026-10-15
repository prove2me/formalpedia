-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning28
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning28
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:09:42.842546+00:00
-- url     : https://prove2.me/theorems/9938dd97-d499-4477-88b8-452a629d137a
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning28
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms43009 through44544. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues28
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins28

theorem TaoFivePrimes.rh_high_height_dirichlet_binning28 :
  RHHighDirichletBinning.bins RHHighDirichletValues28.rows.flatten=
    RHHighDirichletBins28.values.map RHHighDirichletBinning.decode := by sorry
