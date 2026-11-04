-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_padded_folded_correlation
-- name    : ThreeSum.CyclicFold.padded_folded_correlation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:17.115802+00:00
-- url     : https://prove2.me/theorems/78c56c27-430a-44bb-86c7-2b330e55fe6e
-- title:
--   Cyclic Fold: padded folded correlation
-- statement:
--   The Cyclic Fold construction uses the padded folded correlation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L163-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L163-L171

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.padded_folded_correlation {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (n r : ℕ) (hr : r < p) :
    (asPolynomial (padTo n (vector p F)) *
      asPolynomial (padTo n (vector p (fun z => H (-z))))).coeff r +
    (asPolynomial (padTo n (vector p F)) *
      asPolynomial (padTo n (vector p (fun z => H (-z))))).coeff (r+p) =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by sorry
