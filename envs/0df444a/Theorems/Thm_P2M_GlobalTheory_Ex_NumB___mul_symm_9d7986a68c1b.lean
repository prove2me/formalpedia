-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b
-- name    : P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:53.839188+00:00
-- url     : https://prove2.me/theorems/77f65aab-a714-46d5-af85-83a64b138e22
-- title:
--   P2 M Global Theory Ex Num B   mul symm 9d7986a68c1b: P2 M Global Theory Ex Num B   mul symm 9d7986a68c1b
-- statement:
--   The P2 M Global Theory Ex Num B   mul symm 9d7986a68c1b construction uses the P2 M Global Theory Ex Num B   mul symm 9d7986a68c1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulqLaws.lean#L69-L74

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

theorem P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by sorry

alias «GlobalTheory».«Ex».«NumB».«σ_mul_symm» := P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b
