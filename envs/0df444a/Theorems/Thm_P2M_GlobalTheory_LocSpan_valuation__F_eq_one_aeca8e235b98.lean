-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocSpan_valuation__F_eq_one_aeca8e235b98
-- name    : P2M_GlobalTheory_LocSpan_valuation__F_eq_one_aeca8e235b98
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:53.107978+00:00
-- url     : https://prove2.me/theorems/28321dff-cc12-4166-8c67-8e70d64f9891
-- title:
--   P2 M Global Theory Loc Span valuation  F eq one aeca8e235b98: P2 M Global Theory Loc Span valuation  F eq one aeca8e235b98
-- statement:
--   The P2 M Global Theory Loc Span valuation  F eq one aeca8e235b98 construction uses the P2 M Global Theory Loc Span valuation  F eq one aeca8e235b98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L65-L73

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

theorem P2M_GlobalTheory_LocSpan_valuation__F_eq_one_aeca8e235b98 {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (d : 𝓞 F) (hd : d ∉ p.asIdeal) :
    valuation A.Fp (A.ιF (d : F)) = 1 := by sorry

alias «GlobalTheory».«LocSpan».«valuation_ιF_eq_one» := P2M_GlobalTheory_LocSpan_valuation__F_eq_one_aeca8e235b98
