-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_code_correct
-- name    : ThreeSum.TernaryExtensionEncoding.quotient_code_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:14.183749+00:00
-- url     : https://prove2.me/theorems/63d70834-5fe6-4622-a307-522258e0875d
-- title:
--   Ternary Extension Encoding: quotient code correct
-- statement:
--   The Ternary Extension Encoding construction uses the quotient code correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L27-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L27-L47

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

theorem ThreeSum.TernaryExtensionEncoding.quotient_code_correct {f : (ZMod p)[X]} (hf : f.Monic)
    {c x y h r : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree)
    (hy : y<p^f.natDegree) (hr : r<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f)
    (hg : LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
      (LightPolynomialQuotientCheck.expected p f.natDegree (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^f.natDegree)) (codeDigits (p := p) r))
      f.natDegree f.natDegree (2*f.natDegree)) :
    encode hf ((encodedEquiv hf).symm ⟨x,hx⟩*(encodedEquiv hf).symm ⟨y,hy⟩)=r := by sorry
