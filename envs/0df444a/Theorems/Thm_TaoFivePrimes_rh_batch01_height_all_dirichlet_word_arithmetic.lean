-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_dirichlet_word_arithmetic
-- name    : TaoFivePrimes.rh_batch01_height_all_dirichlet_word_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:08:23.0141+00:00
-- url     : https://prove2.me/theorems/5ba2138e-f2f1-4b03-a8bc-5f46e0c88e6c
-- title:
--   TaoFivePrimes.rh_batch01_height_all_dirichlet_word_arithmetic
-- statement:
--   Joins all33 accepted arithmetic packets: each proposed packed word at indexn encodes exactly the actual rational Dirichlet weight, offset and bin for1≤n≤50000. The proof uses a generic bounded block-lookup identity and partitions the index range; it does not repeat the expensive arithmetic. This link is needed to interpret binning certificates analytically.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning

theorem TaoFivePrimes.rh_batch01_height_all_dirichlet_word_arithmetic :
  ∀ n:Nat,1 ≤ n ∧ n≤50000 →
  let w:=RHBatch01AllDirichletWords.word n
  (RHBatch01DirichletArithmetic.compute n).gammaRe=RHHighDirichletBinning.field w 0 ∧
  (RHBatch01DirichletArithmetic.compute n).gammaIm=RHHighDirichletBinning.field w 1 ∧
  RHBatch01DirichletArithmetic.delta n=RHHighDirichletBinning.field w 2 ∧
  RHBatch01DirichletArithmetic.bin n=RHHighDirichletBinning.bin w := by sorry
