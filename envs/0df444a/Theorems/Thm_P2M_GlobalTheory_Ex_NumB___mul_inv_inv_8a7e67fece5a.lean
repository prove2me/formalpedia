-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a
-- name    : P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:05.863065+00:00
-- url     : https://prove2.me/theorems/cfd3b08b-2b1d-438c-a844-adda72058a84
-- title:
--   P2 M Global Theory Ex Num B   mul inv inv 8a7e67fece5a: P2 M Global Theory Ex Num B   mul inv inv 8a7e67fece5a
-- statement:
--   The P2 M Global Theory Ex Num B   mul inv inv 8a7e67fece5a construction uses the P2 M Global Theory Ex Num B   mul inv inv 8a7e67fece5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L65-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by sorry

alias «GlobalTheory».«Ex».«NumB».«θ_mul_inv_inv» := P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a
