-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_first_quotient_code
-- name    : ThreeSum.TernaryExtensionEncoding.first_quotient_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:56.098594+00:00
-- url     : https://prove2.me/theorems/43454f46-9cf8-428b-bd95-75596cf88274
-- title:
--   Ternary Extension Encoding: first quotient code
-- statement:
--   The Ternary Extension Encoding construction uses the first quotient code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L55-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L55-L80

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}

theorem ThreeSum.TernaryExtensionEncoding.first_quotient_code (hf : f.Monic) (hd : 0<f.natDegree)
    {c x y : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree) (hy : y<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) :
    let q := p^f.natDegree
    let result := LightPairSearch.first
      (LightPairSearch.goodCode q (quotientGood (p := p) f.natDegree c x y)) (q*q)
    0<result ∧ (result-1)%q=encodedMul hf x y := by sorry
