-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_rowMenu_coefficient
-- name    : ThreeSum.TernaryExtensionEncoding.rowMenu_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:59.61404+00:00
-- url     : https://prove2.me/theorems/71205841-0dc6-4916-93fd-5e5b856dd5cb
-- title:
--   Ternary Extension Encoding: row Menu coefficient
-- statement:
--   The Ternary Extension Encoding construction uses the row Menu coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L84-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L84-L97

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
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.TernaryExtensionEncoding.rowMenu_coefficient (Λ : ℕ) (ℓ : AdjoinRoot f →ₗ[ZMod p] ZMod p)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    TernaryOriginalRowMenu.seedRow Λ ℓ (x,y) i=ℓ (y*x^i.val) := by sorry
