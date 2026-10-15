-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning04
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:56:45.764571+00:00
-- url     : https://prove2.me/theorems/e3be9165-9b40-48a4-b705-077393722762
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning04
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms6145 through7680. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues04
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins04

theorem TaoFivePrimes.rh_high_height_dirichlet_binning04 :
  RHHighDirichletBinning.bins RHHighDirichletValues04.rows.flatten=
    RHHighDirichletBins04.values.map RHHighDirichletBinning.decode := by sorry
