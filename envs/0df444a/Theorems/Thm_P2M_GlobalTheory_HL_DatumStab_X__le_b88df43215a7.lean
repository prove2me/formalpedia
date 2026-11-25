-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7
-- name    : P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:30:22.037706+00:00
-- url     : https://prove2.me/theorems/df8d3566-cbd6-5cb4-b4c9-c28c976d7b79
-- title:
--   P2 M Global Theory HL Datum Stab X  le b88df43215a7: P2 M Global Theory HL Datum Stab X  le b88df43215a7
-- statement:
--   The P2 M Global Theory HL Datum Stab X  le b88df43215a7 construction uses the P2 M Global Theory HL Datum Stab X  le b88df43215a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L63-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L63-L63

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

theorem P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7 (S : Frames L r k) : S.spanTo S.f' r ≤ S.ME := by sorry

alias «GlobalTheory».«HL».«DatumStab».«X'_le» := P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7
