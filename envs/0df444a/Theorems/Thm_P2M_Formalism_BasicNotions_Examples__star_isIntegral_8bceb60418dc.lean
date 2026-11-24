-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc
-- name    : P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:25.941938+00:00
-- url     : https://prove2.me/theorems/a1e15e77-ac24-4661-b97e-67087fbfcb5c
-- title:
--   P2 M Formalism Basic Notions Examples  star is Integral 8bceb60418dc: P2 M Formalism Basic Notions Examples  star is Integral 8bceb60418dc
-- statement:
--   The P2 M Formalism Basic Notions Examples  star is Integral 8bceb60418dc construction uses the P2 M Formalism Basic Notions Examples  star is Integral 8bceb60418dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L97-L98

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField
open scoped TensorProduct
open IsDedekindDomain
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«star_isIntegral» := P2M_Formalism_BasicNotions_Examples__star_isIntegral_8bceb60418dc
