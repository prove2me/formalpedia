-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_padTo_length
-- name    : ThreeSum.CyclicFold.padTo_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:07.055242+00:00
-- url     : https://prove2.me/theorems/a7a6b707-eac2-4e19-8628-e96b6d939a93
-- title:
--   Cyclic Fold: pad To length
-- statement:
--   The Cyclic Fold construction uses the pad To length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L142-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L142-L144

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.padTo_length (n : ℕ) (as : List ℤ) (ha : as.length ≤ n) :
    (padTo n as).length = n := by sorry
