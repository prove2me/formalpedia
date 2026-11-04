-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_folded_correlation
-- name    : ThreeSum.CyclicFold.folded_correlation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:17.865964+00:00
-- url     : https://prove2.me/theorems/145387fa-a939-417c-a18a-d50db7f838cc
-- title:
--   Cyclic Fold: folded correlation
-- statement:
--   The Cyclic Fold construction uses the folded correlation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L130-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L130-L137

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.folded_correlation {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff r +
      (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff (r+p) =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by sorry
