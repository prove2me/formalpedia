-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_check_iff
-- name    : ThreeSum.TernaryExtensionEncoding.quotient_check_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:24.104551+00:00
-- url     : https://prove2.me/theorems/c86e8553-2c3b-455d-bb1b-6d4916446434
-- title:
--   Ternary Extension Encoding: quotient check iff
-- statement:
--   The Ternary Extension Encoding construction uses the quotient check iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L34-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L34-L51

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.quotient_check_iff {d c h r : ℕ} (hc : c<p^d) (hr : r<p^d)
    (x y : ℕ → ℕ) :
    LightPolynomialProductCheck.Valid p x y
      (LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
        (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r)) d d (2*d) ↔
    arrayPolynomial d x*arrayPolynomial (p := p) d y=
      vectorPolynomial (coefficientVector d h)*monicOfCode d c+
        vectorPolynomial (coefficientVector d r) := by sorry
