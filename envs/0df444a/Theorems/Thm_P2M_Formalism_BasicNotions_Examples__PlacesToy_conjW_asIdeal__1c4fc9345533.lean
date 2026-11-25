-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:09.85327+00:00
-- url     : https://prove2.me/theorems/4f14ab2e-fa97-4885-8fa6-638621bfe12d
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal  1c4fc9345533: P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal  1c4fc9345533
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal  1c4fc9345533 construction uses the P2 M Formalism Basic Notions Examples  Places Toy conj W as Ideal  1c4fc9345533 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L236-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L236-L240

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

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533 (w : HeightOneSpectrum (𝓞 K)) :
    (conjW w).asIdeal = w.asIdeal.map (starO (K := K)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«conjW_asIdeal'» := P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533
