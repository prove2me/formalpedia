-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668
-- name    : P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:22.395742+00:00
-- url     : https://prove2.me/theorems/fdf263f3-24c0-436b-b40b-a24c2836b184
-- title:
--   P2 M Formalism Basic Notions Examples  Places Toy v Add conj W 59bcae034668: P2 M Formalism Basic Notions Examples  Places Toy v Add conj W 59bcae034668
-- statement:
--   The P2 M Formalism Basic Notions Examples  Places Toy v Add conj W 59bcae034668 construction uses the P2 M Formalism Basic Notions Examples  Places Toy v Add conj W 59bcae034668 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L287-L290

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

theorem P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668 (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    vAdd (conjW w) x = vAdd w (star x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«PlacesToy».«vAdd_conjW» := P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668
