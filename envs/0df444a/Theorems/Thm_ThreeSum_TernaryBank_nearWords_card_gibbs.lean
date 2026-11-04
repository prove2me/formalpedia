-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs
-- name    : ThreeSum.TernaryBank.nearWords_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:49.403253+00:00
-- url     : https://prove2.me/theorems/cb306b89-62f8-4e5d-afac-dd789a406d9a
-- title:
--   Ternary Bank: near Words card gibbs
-- statement:
--   The Ternary Bank construction uses the near Words card gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L191-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L191-L206

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType

theorem ThreeSum.TernaryBank.nearWords_card_gibbs {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by sorry
