-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_factor_nohit_iff
-- name    : ThreeSum.TernaryExtensionEncoding.factor_nohit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:48.993216+00:00
-- url     : https://prove2.me/theorems/1b6bb13d-12b4-4e1c-aa46-e41f6af5cca5
-- title:
--   Ternary Extension Encoding: factor nohit iff
-- statement:
--   The Ternary Extension Encoding construction uses the factor nohit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L49-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSearchCorrect.lean#L49-L66

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

theorem ThreeSum.TernaryExtensionEncoding.factor_nohit_iff {d e c : ℕ} (hd : 0<d) (he : 0<e) (hed : e<d)
    (hc : c<p^d) :
    (∀ u<p^e, ∀ v<p^(d-e),
      ¬LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
        (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d))
        (e+1) (d-e+1) (2*d)) ↔
    ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
      monicCandidate a*monicCandidate b≠monicOfCode d c := by sorry
