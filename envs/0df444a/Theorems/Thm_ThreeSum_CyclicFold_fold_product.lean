-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_fold_product
-- name    : ThreeSum.CyclicFold.fold_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:09.488638+00:00
-- url     : https://prove2.me/theorems/50d134c6-4172-4b7e-8143-9f7dfbfbefaa
-- title:
--   Cyclic Fold: fold product
-- statement:
--   The Cyclic Fold construction uses the fold product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L52-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L52-L64

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.fold_product (as bs : List ℤ) (p r : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (hr : r < p) :
    (asPolynomial as * asPolynomial bs).coeff r +
      (asPolynomial as * asPolynomial bs).coeff (r + p) = cyclic p as bs r := by sorry
