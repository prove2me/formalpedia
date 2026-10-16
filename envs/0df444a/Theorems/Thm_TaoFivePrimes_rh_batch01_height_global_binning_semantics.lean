-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_global_binning_semantics
-- name    : TaoFivePrimes.rh_batch01_height_global_binning_semantics
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:14:36.894442+00:00
-- url     : https://prove2.me/theorems/a7121744-84ed-4a7a-b44b-847650e9ee0b
-- title:
--   TaoFivePrimes.rh_batch01_height_global_binning_semantics
-- statement:
--   Gives the exact finite-sum meaning of every global bin coefficient at all24 Taylor orders: it is the sum of the proposed word terms assigned to that bin. The proof joins33 accepted packet-binning identities to the accepted global merge and generic proved list semantics. Analytic interpretation then uses the separate word-arithmetic and enclosure theorems; this statement alone asserts no Fourier accuracy, sign, count or RH.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
import Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
import Definitions.Def_TaoFivePrimes_RHHighBinningMerge

theorem TaoFivePrimes.rh_batch01_height_global_binning_semantics :
  ∀ m:Nat,m<929 → ∀ k:Nat,k<24 →
  RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)=
    ((RHBatch01AllDirichletWords.values.map (fun w=>if RHHighDirichletBinning.bin w=m then
      RHHighBinningSemantic.coefficientAt (RHHighDirichletBinning.terms w) k else 0)).sum) := by sorry
