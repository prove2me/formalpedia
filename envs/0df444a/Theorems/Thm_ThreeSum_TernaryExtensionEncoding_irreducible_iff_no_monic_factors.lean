-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_irreducible_iff_no_monic_factors
-- name    : ThreeSum.TernaryExtensionEncoding.irreducible_iff_no_monic_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:35.600762+00:00
-- url     : https://prove2.me/theorems/141860bb-5856-4185-b18c-8cceb9c734b4
-- title:
--   Ternary Extension Encoding: irreducible iff no monic factors
-- statement:
--   The Ternary Extension Encoding construction uses the irreducible iff no monic factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L13-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean#L13-L44

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.irreducible_iff_no_monic_factors {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hdeg : f.natDegree=d) (hd : 0<d) :
    Irreducible f ↔ ∀ e, 0<e → e<d →
      ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
        monicCandidate a*monicCandidate b≠f := by sorry
