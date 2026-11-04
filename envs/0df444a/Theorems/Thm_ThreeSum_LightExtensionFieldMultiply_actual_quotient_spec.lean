-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionFieldMultiply_actual_quotient_spec
-- name    : ThreeSum.LightExtensionFieldMultiply.actual_quotient_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:42.887189+00:00
-- url     : https://prove2.me/theorems/f80794e2-42ad-4d74-b8e0-48592e344a29
-- title:
--   Light Extension Field Multiply: actual quotient spec
-- statement:
--   The Light Extension Field Multiply construction uses the actual quotient spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFieldMultiply.lean#L11-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFieldMultiply.lean#L11-L33

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionFieldMultiply
open Light TernaryExtensionEncoding
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightExtensionFieldMultiply._p2m_local_instance_74f6067cfd_8
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}

theorem ThreeSum.LightExtensionFieldMultiply.actual_quotient_spec (C : LightExtensionQuotientPredicate.Layout)
    (hCp : C.p=p) (hCd : C.dim=f.natDegree) (hf : f.Monic) (hd : 0 < f.natDegree)
    {c : ℕ} (hc : c < p^f.natDegree) (hm : monicOfCode (p := p) f.natDegree c=f) :
    ∀ a < p^f.natDegree, ∀ b < p^f.natDegree,
      let q := p^f.natDegree
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b)
          (codeDigits (p := p) (c+p^f.natDegree)))) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=encodedMul hf a b := by sorry
