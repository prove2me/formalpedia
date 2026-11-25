-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_Glue_smul_mem_of_mem__8d07f3110088
-- name    : P2M_GlobalTheory_HL_Glue_smul_mem_of_mem__8d07f3110088
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:44.488521+00:00
-- url     : https://prove2.me/theorems/0483cb21-985e-47a8-93f3-309e8134791d
-- title:
--   P2 M Global Theory HL Glue smul mem of mem  8d07f3110088: P2 M Global Theory HL Glue smul mem of mem  8d07f3110088
-- statement:
--   The P2 M Global Theory HL Glue smul mem of mem  8d07f3110088 construction uses the P2 M Global Theory HL Glue smul mem of mem  8d07f3110088 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLattices.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLattices.lean#L18-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem P2M_GlobalTheory_HL_Glue_smul_mem_of_mem__8d07f3110088 (Λ : Submodule O (Fin n → R)) {c : R} (hc : c ∈ O) {x : Fin n → R}
    (hx : x ∈ Λ) : c • x ∈ Λ := by sorry

alias «GlobalTheory».«HL».«Glue».«smul_mem_of_mem'» := P2M_GlobalTheory_HL_Glue_smul_mem_of_mem__8d07f3110088
