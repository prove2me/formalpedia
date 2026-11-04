-- Prove2me | Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_sum
-- name    : ThreeSum.CyclicFold.asPolynomial_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:01.078763+00:00
-- url     : https://prove2.me/theorems/bf04cc94-9db9-4aa9-8c05-d82ea387e788
-- title:
--   Cyclic Fold: as Polynomial sum
-- statement:
--   The Cyclic Fold construction uses the as Polynomial sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L20-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CyclicFold.lean#L20-L28

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold
set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators

theorem ThreeSum.CyclicFold.asPolynomial_sum (as : List ℤ) (p : ℕ) (ha : as.length ≤ p) :
    asPolynomial as = ∑ i ∈ Finset.range p, monomial i (as.getD i 0) := by sorry
