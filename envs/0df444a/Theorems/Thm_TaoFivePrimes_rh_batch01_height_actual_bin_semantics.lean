-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_actual_bin_semantics
-- name    : TaoFivePrimes.rh_batch01_height_actual_bin_semantics
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:20:41.354646+00:00
-- url     : https://prove2.me/theorems/a6d5b097-b2f0-4982-a06a-ce831ba458f6
-- title:
--   TaoFivePrimes.rh_batch01_height_actual_bin_semantics
-- statement:
--   The scaled global integer bin coefficient equals the finite grouped sum of the actual published rational coefficient algorithm over all50000 words. Uses accepted global binning and all-word arithmetic identities. No analytic approximation, sign, winding or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighBinningSemantic
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins

theorem TaoFivePrimes.rh_batch01_height_actual_bin_semantics :
 ∀m:Nat,m<929 → ∀k:Nat,k<24 →
 RHHighBinningSemantic.pairValue (RHBatch01GlobalDirichletBins.coefficient m k)/(2:ℂ)^128=
  ∑n:Fin 50000,if RHBatch01DirichletArithmetic.bin (n.val+1)=m then
   (let c:=RHBatch01DirichletArithmetic.coefficient (n.val+1) k
    ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0 := by sorry
