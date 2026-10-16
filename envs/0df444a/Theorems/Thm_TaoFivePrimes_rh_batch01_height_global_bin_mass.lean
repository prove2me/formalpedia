-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_global_bin_mass
-- name    : TaoFivePrimes.rh_batch01_height_global_bin_mass
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:25:09.372935+00:00
-- url     : https://prove2.me/theorems/c087c3b8-b08e-4725-865c-a4bfa0ff56a9
-- title:
--   TaoFivePrimes.rh_batch01_height_global_bin_mass
-- statement:
--   Ordinary kernel verification that the complete proposed929-bin,24-order table has total real/imaginary component mass at most100 after128-bit scaling. A linear traversal of packed words avoids repeated indexed lookups. This exact finite bound supplies an efficient analytic correlation-error budget but asserts no Fourier accuracy, sign, count, or RH.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins

theorem TaoFivePrimes.rh_batch01_height_global_bin_mass :
  RHBatch01GlobalDirichletBins.values.length=929 ∧
  ((RHBatch01GlobalDirichletBins.values.map (fun w=>
    ((RHHighDirichletBinning.decodeCoefficients 24 w).map (fun p=>p.1.natAbs+p.2.natAbs)).sum)).sum)≤100*2^128 := by sorry
