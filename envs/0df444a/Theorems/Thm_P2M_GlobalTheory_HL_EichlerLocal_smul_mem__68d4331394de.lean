-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de
-- name    : P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:13.859738+00:00
-- url     : https://prove2.me/theorems/f0bc9abe-b214-485c-a908-cb4c8a337033
-- title:
--   P2 M Global Theory HL Eichler Local smul mem  68d4331394de: P2 M Global Theory HL Eichler Local smul mem  68d4331394de
-- statement:
--   The P2 M Global Theory HL Eichler Local smul mem  68d4331394de construction uses the P2 M Global Theory HL Eichler Local smul mem  68d4331394de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerLatticeLocallyConstantData.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerLatticeLocallyConstantData.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerLocal
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de {Λ : Submodule L.O (Fin n → E)} {a : E} (ha : a ∈ L.O) {v : Fin n → E}
    (hv : v ∈ Λ) : a • v ∈ Λ := by sorry

alias «GlobalTheory».«HL».«EichlerLocal».«smul_mem'» := P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de
