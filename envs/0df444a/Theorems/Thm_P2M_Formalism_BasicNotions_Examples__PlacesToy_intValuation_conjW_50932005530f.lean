-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:08.454471+00:00
-- url     : https://prove2.me/theorems/47a8738d-559b-4f7b-8393-fbfc6499e66c
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy int Valuation conj W 50932005530f: P2 M Formalism Basic Notions Examples  Places Toy int Valuation conj W 50932005530f
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy int Valuation conj W 50932005530f construction uses the P2 M Formalism Basic Notions Examples  Places Toy int Valuation conj W 50932005530f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L253-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L253-L273

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (conjW w).intValuation r = w.intValuation (starO r) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«intValuation_conjW» := P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f
