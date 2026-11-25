-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80
-- name    : P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:17:57.785157+00:00
-- url     : https://prove2.me/theorems/46c20ac7-3e1c-44cd-86c4-77e397b328e3
-- title:
--   P2 M Global Theory HL Glue  E mem 8736254c8d80: P2 M Global Theory HL Glue  E mem 8736254c8d80
-- statement:
--   The P2 M Global Theory HL Glue  E mem 8736254c8d80 construction uses the P2 M Global Theory HL Glue  E mem 8736254c8d80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanSingleIff.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemSpanSingleIff.lean#L46-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80 (A : _root_.GlobalTheory.HL.Places F E sig)
    (p : HeightOneSpectrum (𝓞 F)) (x : E) (hx : IsIntegral ℤ x) :
    (A.loc p).ιE x ∈ (A.L p).O := by sorry

alias «GlobalTheory».«HL».«Glue».«ιE_mem» := P2M_GlobalTheory_HL_Glue__E_mem_8736254c8d80
