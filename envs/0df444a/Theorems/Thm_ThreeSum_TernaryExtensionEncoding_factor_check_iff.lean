-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_factor_check_iff
-- name    : ThreeSum.TernaryExtensionEncoding.factor_check_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:32.49397+00:00
-- url     : https://prove2.me/theorems/5624fe9f-692a-43de-8a8c-60bdc42cf16a
-- title:
--   Ternary Extension Encoding: factor check iff
-- statement:
--   The Ternary Extension Encoding construction uses the factor check iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L53-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L53-L63

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

theorem ThreeSum.TernaryExtensionEncoding.factor_check_iff {d e c u v : ℕ} (hd : 0<d) (he : e<d)
    (hc : c<p^d) (hu : u<p^e) (hv : v<p^(d-e)) :
    LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
      (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d)) (e+1) (d-e+1) (2*d) ↔
    monicOfCode (p := p) e u*monicOfCode (d-e) v=monicOfCode d c := by sorry
