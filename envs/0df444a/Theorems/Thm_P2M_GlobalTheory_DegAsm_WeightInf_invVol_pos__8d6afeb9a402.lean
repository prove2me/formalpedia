-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DegAsm_WeightInf_invVol_pos__8d6afeb9a402
-- name    : P2M_GlobalTheory_DegAsm_WeightInf_invVol_pos__8d6afeb9a402
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:56:02.656865+00:00
-- url     : https://prove2.me/theorems/55a157b2-2b1a-4efb-92cb-3654d2362f0d
-- title:
--   P2 M Global Theory Deg Asm Weight Inf inv Vol pos  8d6afeb9a402: P2 M Global Theory Deg Asm Weight Inf inv Vol pos  8d6afeb9a402
-- statement:
--   The P2 M Global Theory Deg Asm Weight Inf inv Vol pos  8d6afeb9a402 construction uses the P2 M Global Theory Deg Asm Weight Inf inv Vol pos  8d6afeb9a402 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolPos.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolPos.lean#L20-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.WeightInf

theorem P2M_GlobalTheory_DegAsm_WeightInf_invVol_pos__8d6afeb9a402 {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by sorry

alias «GlobalTheory».«DegAsm».«WeightInf».«invVol_pos'» := P2M_GlobalTheory_DegAsm_WeightInf_invVol_pos__8d6afeb9a402
