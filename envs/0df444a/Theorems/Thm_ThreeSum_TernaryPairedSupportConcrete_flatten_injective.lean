-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_flatten_injective
-- name    : ThreeSum.TernaryPairedSupportConcrete.flatten_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:35.398714+00:00
-- url     : https://prove2.me/theorems/9a5c049f-23c4-4fa6-8795-f7cb28c2a7bb
-- title:
--   Ternary Paired Support Concrete: flatten injective
-- statement:
--   The Ternary Paired Support Concrete construction uses the flatten injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L27-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean#L27-L37

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryPairedSupportConcrete.flatten_injective (J : ℕ) : Function.Injective (flatten (K := K) J) := by sorry
