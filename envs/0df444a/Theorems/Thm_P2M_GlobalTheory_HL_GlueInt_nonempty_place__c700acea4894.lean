-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894
-- name    : P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:04.790532+00:00
-- url     : https://prove2.me/theorems/7df086e9-859f-409b-94c3-9a3d4570a7bb
-- title:
--   P2 M Global Theory HL Glue Int nonempty place  c700acea4894: P2 M Global Theory HL Glue Int nonempty place  c700acea4894
-- statement:
--   The P2 M Global Theory HL Glue Int nonempty place  c700acea4894 construction uses the P2 M Global Theory HL Glue Int nonempty place  c700acea4894 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfIntegralAllQuadraticCompletions.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfIntegralAllQuadraticCompletions.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlueInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894 : Nonempty (HeightOneSpectrum (𝓞 F)) := by sorry

alias «GlobalTheory».«HL».«GlueInt».«nonempty_place'» := P2M_GlobalTheory_HL_GlueInt_nonempty_place__c700acea4894
