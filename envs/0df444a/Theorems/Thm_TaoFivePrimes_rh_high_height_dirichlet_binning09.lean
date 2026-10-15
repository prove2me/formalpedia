-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning09
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning09
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:20:10.838139+00:00
-- url     : https://prove2.me/theorems/faf80391-b507-4048-8e47-55db529de3e3
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning09
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms13825 through15360. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues09
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins09

theorem TaoFivePrimes.rh_high_height_dirichlet_binning09 :
  RHHighDirichletBinning.bins RHHighDirichletValues09.rows.flatten=
    RHHighDirichletBins09.values.map RHHighDirichletBinning.decode := by sorry
