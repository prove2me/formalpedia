-- Prove2me | Theorems.Thm_ThreeSum_TernaryReconstruction_recover_binomialZeta
-- name    : ThreeSum.TernaryReconstruction.recover_binomialZeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:52.033209+00:00
-- url     : https://prove2.me/theorems/339b954f-52e1-4e1c-b2f0-761bcec18874
-- title:
--   Ternary Reconstruction: recover binomial Zeta
-- statement:
--   The Ternary Reconstruction construction uses the recover binomial Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L58-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L58-L63

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryReconstruction.recover_binomialZeta {N h T : ℕ} (hcut : h ≤ T)
    (f seed : TritWord N → ℤ) (hf : ∀ A, f A ≠ 0 → rank A = h)
    (hbank : ∀ R ∈ bank N T, seed R = binomialZeta f R) (R : TritWord N) :
    recover seed h T (rank R - T) R = binomialZeta f R := by sorry
