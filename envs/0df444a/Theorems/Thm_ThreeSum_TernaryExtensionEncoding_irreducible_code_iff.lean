-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_irreducible_code_iff
-- name    : ThreeSum.TernaryExtensionEncoding.irreducible_code_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:23.820138+00:00
-- url     : https://prove2.me/theorems/f0fc2a8a-053e-48ce-9bae-d4a210d2f6e2
-- title:
--   Ternary Extension Encoding: irreducible code iff
-- statement:
--   The Ternary Extension Encoding construction uses the irreducible code iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L65-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L65-L77

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

theorem ThreeSum.TernaryExtensionEncoding.irreducible_code_iff {d c : ℕ} (hd : 0<d) :
    Irreducible (monicOfCode (p := p) d c) ↔
    ∀ e, 0<e → e<d → ∀ u<p^e, ∀ v<p^(d-e),
      monicOfCode (p := p) e u*monicOfCode (d-e) v≠monicOfCode d c := by sorry
