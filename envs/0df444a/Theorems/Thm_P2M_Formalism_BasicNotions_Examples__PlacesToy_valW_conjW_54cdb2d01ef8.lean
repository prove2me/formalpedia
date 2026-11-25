-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:24.352289+00:00
-- url     : https://prove2.me/theorems/958d416a-41ef-43a5-82d6-5b65ab9ccf66
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy val W conj W 54cdb2d01ef8: P2 M Formalism Basic Notions Examples  Places Toy val W conj W 54cdb2d01ef8
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy val W conj W 54cdb2d01ef8 construction uses the P2 M Formalism Basic Notions Examples  Places Toy val W conj W 54cdb2d01ef8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L292-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L292-L297

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

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8 (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    valW (conjW w) x = valW w (star x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«valW_conjW» := P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8
