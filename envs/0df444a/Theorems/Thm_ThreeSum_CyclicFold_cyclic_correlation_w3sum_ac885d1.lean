-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_cyclic_correlation_w3sum_ac885d1
-- name    : ThreeSum.CyclicFold.cyclic_correlation_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:05.804758+00:00
-- url     : https://prove2.me/theorems/b134099c-e657-4f8d-8eac-dc8064e825c2
-- title:
--   Cyclic Fold: cyclic correlation
-- statement:
--   The Cyclic Fold construction uses the cyclic correlation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L91-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L91-L128

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.cyclic_correlation_w3sum_ac885d1 {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    cyclic p (vector p F) (vector p (fun z => H (-z))) r =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by sorry
