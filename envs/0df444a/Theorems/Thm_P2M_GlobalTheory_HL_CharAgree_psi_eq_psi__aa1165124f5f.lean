-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_CharAgree_psi_eq_psi__aa1165124f5f
-- name    : P2M_GlobalTheory_HL_CharAgree_psi_eq_psi__aa1165124f5f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:12.728427+00:00
-- url     : https://prove2.me/theorems/3a4ef0d4-53c3-5744-a2ab-4d6389465951
-- title:
--   P2 M Global Theory HL Char Agree psi eq psi  aa1165124f5f: P2 M Global Theory HL Char Agree psi eq psi  aa1165124f5f
-- statement:
--   The P2 M Global Theory HL Char Agree psi eq psi  aa1165124f5f construction uses the P2 M Global Theory HL Char Agree psi eq psi  aa1165124f5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L167-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliser.lean#L167-L205

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliser
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem P2M_GlobalTheory_HL_CharAgree_psi_eq_psi__aa1165124f5f : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by sorry

alias «GlobalTheory».«HL».«CharAgree».«psi_eq_psi'» := P2M_GlobalTheory_HL_CharAgree_psi_eq_psi__aa1165124f5f
