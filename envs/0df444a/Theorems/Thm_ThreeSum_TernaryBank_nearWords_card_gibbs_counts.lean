-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts
-- name    : ThreeSum.TernaryBank.nearWords_card_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:45.855551+00:00
-- url     : https://prove2.me/theorems/a0d503bf-64ec-4330-9f16-cd823274ec2e
-- title:
--   Ternary Bank: near Words card gibbs counts
-- statement:
--   The Ternary Bank construction uses the near Words card gibbs counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L208-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L208-L213

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

theorem ThreeSum.TernaryBank.nearWords_card_gibbs_counts {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by sorry
