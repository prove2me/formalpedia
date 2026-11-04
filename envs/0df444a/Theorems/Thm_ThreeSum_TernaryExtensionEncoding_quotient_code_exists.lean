-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_code_exists
-- name    : ThreeSum.TernaryExtensionEncoding.quotient_code_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:55.955774+00:00
-- url     : https://prove2.me/theorems/260a94be-2ad1-4a8e-81ea-ffad12edd511
-- title:
--   Ternary Extension Encoding: quotient code exists
-- statement:
--   The Ternary Extension Encoding construction uses the quotient code exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L11-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L11-L25

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.quotient_code_exists {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) {c : ℕ} (hc : c<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) (x y : ℕ) :
    ∃ h<p^f.natDegree, ∃ r<p^f.natDegree,
      LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
        (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
          (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
        f.natDegree f.natDegree (2*f.natDegree) := by sorry
