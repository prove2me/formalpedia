-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal_18051fd2f415
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal_18051fd2f415
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:46.214085+00:00
-- url     : https://prove2.me/theorems/5d35cd3f-2148-5050-a905-e4057f5df54b
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal 18051fd2f415: P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal 18051fd2f415
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal 18051fd2f415 construction uses the P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal 18051fd2f415 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L232-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L232-L233

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
omit [NumberField K]

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal_18051fd2f415 (w : HeightOneSpectrum (𝓞 K)) :
    (conjW w).asIdeal = w.asIdeal.comap ((starO (K := K)).symm : 𝓞 K →+* 𝓞 K) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«conjW_asIdeal» := P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal_18051fd2f415
