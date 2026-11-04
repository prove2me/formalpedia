-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_product_of_relation
-- name    : ThreeSum.TernaryExtensionEncoding.quotient_product_of_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:57.429963+00:00
-- url     : https://prove2.me/theorems/f20d8c12-d51e-46c1-a638-db5801cc15d9
-- title:
--   Ternary Extension Encoding: quotient product of relation
-- statement:
--   The Ternary Extension Encoding construction uses the quotient product of relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L39-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean#L39-L44

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.quotient_product_of_relation {f : (ZMod p)[X]} (hf : f.Monic)
    (x y : AdjoinRoot f) (h r : Fin f.natDegree → ZMod p)
    (hr : remainderRelation (coefficients hf x) (coefficients hf y) h r) :
    coefficients hf (x*y)=r := by sorry
