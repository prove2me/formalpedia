-- Prove2me | Theorems.Thm_ThreeSum_TernaryReconstruction_recover_eq
-- name    : ThreeSum.TernaryReconstruction.recover_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:51.656831+00:00
-- url     : https://prove2.me/theorems/7f8293e5-e990-43e0-91ba-d44e8533d7df
-- title:
--   Ternary Reconstruction: recover eq
-- statement:
--   The Ternary Reconstruction construction uses the recover eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L28-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L28-L56

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryReconstruction.recover_eq {N h T : ℕ} (hcut : h ≤ T) (seed F : TritWord N → ℤ)
    (hbank : ∀ R ∈ bank N T, seed R = F R)
    (hEuler : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (fuel : ℕ) (R : TritWord N) (hbound : rank R ≤ T + fuel) :
    recover seed h T fuel R = F R := by sorry
