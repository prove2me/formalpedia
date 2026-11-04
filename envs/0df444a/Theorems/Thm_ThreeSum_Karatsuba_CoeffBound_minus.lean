-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_minus
-- name    : ThreeSum.Karatsuba.CoeffBound.minus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:52.601324+00:00
-- url     : https://prove2.me/theorems/160d0acf-e3d6-4e3c-aa0c-c8c8a4750955
-- title:
--   Coeff Bound: minus
-- statement:
--   The Coeff Bound construction uses the minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L68-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L68-L72

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators

theorem ThreeSum.Karatsuba.CoeffBound.minus {as bs : List ℤ} {U V : ℤ}
    (ha : CoeffBound as U) (hb : CoeffBound bs V) : CoeffBound (minus as bs) (U + V) := by sorry
