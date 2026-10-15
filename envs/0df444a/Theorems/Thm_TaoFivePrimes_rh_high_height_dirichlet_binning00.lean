-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning00
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning00
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T03:37:28.711985+00:00
-- url     : https://prove2.me/theorems/040c944f-fd3a-46d3-911f-657d96b7b768
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning00
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms1 through1536. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues00
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins00

theorem TaoFivePrimes.rh_high_height_dirichlet_binning00 :
  RHHighDirichletBinning.bins RHHighDirichletValues00.rows.flatten=
    RHHighDirichletBins00.values.map RHHighDirichletBinning.decode := by sorry
