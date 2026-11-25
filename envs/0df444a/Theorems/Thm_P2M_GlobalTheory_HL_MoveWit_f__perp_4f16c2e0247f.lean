-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_MoveWit_f__perp_4f16c2e0247f
-- name    : P2M_GlobalTheory_HL_MoveWit_f__perp_4f16c2e0247f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:55.150231+00:00
-- url     : https://prove2.me/theorems/266bbac3-cb80-4ee0-bf72-f8d3da455393
-- title:
--   P2 M Global Theory HL Move Wit f  perp 4f16c2e0247f: P2 M Global Theory HL Move Wit f  perp 4f16c2e0247f
-- statement:
--   The P2 M Global Theory HL Move Wit f  perp 4f16c2e0247f construction uses the P2 M Global Theory HL Move Wit f  perp 4f16c2e0247f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L155-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MoveLatticeIsTermSameDatumWithWitnesses.lean#L155-L165

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

theorem P2M_GlobalTheory_HL_MoveWit_f__perp_4f16c2e0247f (b : Fin (r + 1)) : S.f' b ∈ perp L S.Hm S.X' := by sorry

alias «GlobalTheory».«HL».«MoveWit».«f'_perp» := P2M_GlobalTheory_HL_MoveWit_f__perp_4f16c2e0247f
