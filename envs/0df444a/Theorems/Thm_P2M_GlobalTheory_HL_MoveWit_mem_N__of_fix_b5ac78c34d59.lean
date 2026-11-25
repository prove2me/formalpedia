-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_MoveWit_mem_N__of_fix_b5ac78c34d59
-- name    : P2M_GlobalTheory_HL_MoveWit_mem_N__of_fix_b5ac78c34d59
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:07.216845+00:00
-- url     : https://prove2.me/theorems/42fdc356-8f10-4a27-baec-3115fcec7ebe
-- title:
--   P2 M Global Theory HL Move Wit mem N  of fix b5ac78c34d59: P2 M Global Theory HL Move Wit mem N  of fix b5ac78c34d59
-- statement:
--   The P2 M Global Theory HL Move Wit mem N  of fix b5ac78c34d59 construction uses the P2 M Global Theory HL Move Wit mem N  of fix b5ac78c34d59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L173-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L173-L178

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem P2M_GlobalTheory_HL_MoveWit_mem_N__of_fix_b5ac78c34d59 {g : S.GLV} (hg : g ∈ isomG L S.Hm) (h : ∀ v ∈ perp L S.Hm S.X', g v = v) :
    g ∈ S.N' := by sorry

alias «GlobalTheory».«HL».«MoveWit».«mem_N'_of_fix» := P2M_GlobalTheory_HL_MoveWit_mem_N__of_fix_b5ac78c34d59
