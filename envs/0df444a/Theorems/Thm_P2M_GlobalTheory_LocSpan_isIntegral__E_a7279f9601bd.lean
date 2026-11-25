-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd
-- name    : P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:47.686993+00:00
-- url     : https://prove2.me/theorems/127df340-977f-4459-bc8f-9a4d8f0f451e
-- title:
--   P2 M Global Theory Loc Span is Integral  E a7279f9601bd: P2 M Global Theory Loc Span is Integral  E a7279f9601bd
-- statement:
--   The P2 M Global Theory Loc Span is Integral  E a7279f9601bd construction uses the P2 M Global Theory Loc Span is Integral  E a7279f9601bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L50-L52

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
omit [StarRing E]

theorem P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
    (x : 𝓞 E) : IsIntegral 𝒪[A.Fp] (A.ιE (x : E)) := by sorry

alias «GlobalTheory».«LocSpan».«isIntegral_ιE» := P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd
