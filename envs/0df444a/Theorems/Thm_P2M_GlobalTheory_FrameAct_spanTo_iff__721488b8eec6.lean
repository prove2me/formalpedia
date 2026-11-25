-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
-- name    : P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:49.409752+00:00
-- url     : https://prove2.me/theorems/3a09d2cc-fafe-5fb2-88aa-6a1bd716975c
-- title:
--   P2 M Global Theory Frame Act span To iff  721488b8eec6: P2 M Global Theory Frame Act span To iff  721488b8eec6
-- statement:
--   The P2 M Global Theory Frame Act span To iff  721488b8eec6 construction uses the P2 M Global Theory Frame Act span To iff  721488b8eec6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesStabilizerActsOnTerms.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramesStabilizerActsOnTerms.lean#L156-L160

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
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
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6 (h : S.GLV) (hh : h ∈ S.St) (J : ℕ) (v : S.V) :
    h v ∈ S.spanTo S.f' J ↔ v ∈ S.spanTo S.f' J := by sorry

alias «GlobalTheory».«FrameAct».«spanTo_iff'» := P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
