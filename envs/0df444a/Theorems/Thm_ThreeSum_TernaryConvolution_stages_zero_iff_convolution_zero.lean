-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_stages_zero_iff_convolution_zero
-- name    : ThreeSum.TernaryConvolution.stages_zero_iff_convolution_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:16.851084+00:00
-- url     : https://prove2.me/theorems/fb1655cd-2eb8-41a0-9950-1e1a51282a5e
-- title:
--   Ternary Convolution: stages zero iff convolution zero
-- statement:
--   The Ternary Convolution construction uses the stages zero iff convolution zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L313-L322
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L313-L322

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryConvolution.stages_zero_iff_convolution_zero {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q=0 ↔
      convolution f g Q=0 := by sorry
