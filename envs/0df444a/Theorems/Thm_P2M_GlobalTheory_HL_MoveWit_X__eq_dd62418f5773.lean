-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773
-- name    : P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:34.14853+00:00
-- url     : https://prove2.me/theorems/3a6c77a5-0f21-5999-84b9-22752223b89b
-- title:
--   P2 M Global Theory HL Move Wit X  eq dd62418f5773: P2 M Global Theory HL Move Wit X  eq dd62418f5773
-- statement:
--   The P2 M Global Theory HL Move Wit X  eq dd62418f5773 construction uses the P2 M Global Theory HL Move Wit X  eq dd62418f5773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L145-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L145-L153

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

theorem P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773 : Submodule.span E (Set.range fun j : Fin r => S.f' j.castSucc) = S.X' := by sorry

alias «GlobalTheory».«HL».«MoveWit».«X'_eq» := P2M_GlobalTheory_HL_MoveWit_X__eq_dd62418f5773
