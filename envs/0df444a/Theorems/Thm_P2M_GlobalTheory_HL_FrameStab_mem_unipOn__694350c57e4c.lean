-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c
-- name    : P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:02.607509+00:00
-- url     : https://prove2.me/theorems/0df9a95c-9ffe-56d9-86e0-2f8f82e30753
-- title:
--   P2 M Global Theory HL Frame Stab mem unip On  694350c57e4c: P2 M Global Theory HL Frame Stab mem unip On  694350c57e4c
-- statement:
--   The P2 M Global Theory HL Frame Stab mem unip On  694350c57e4c construction uses the P2 M Global Theory HL Frame Stab mem unip On  694350c57e4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCommonStabiliserEqPairingMatrixStabiliser.lean#L17-L25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c [IsArtinianRing E] {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) : g ∈ unipOn A B := by sorry

alias «GlobalTheory».«HL».«FrameStab».«mem_unipOn'» := P2M_GlobalTheory_HL_FrameStab_mem_unipOn__694350c57e4c
