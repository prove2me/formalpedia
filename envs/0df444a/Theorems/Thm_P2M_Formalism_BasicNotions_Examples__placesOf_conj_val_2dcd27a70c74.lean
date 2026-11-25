-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__placesOf_conj_val_2dcd27a70c74
-- name    : P2M_Formalism_BasicNotions_Examples__placesOf_conj_val_2dcd27a70c74
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:16.566308+00:00
-- url     : https://prove2.me/theorems/aebe4500-ef8a-4554-8f91-c01bea4460f8
-- title:
--   P2 M Formalism Basic Notions Examples  places Of conj val 2dcd27a70c74: P2 M Formalism Basic Notions Examples  places Of conj val 2dcd27a70c74
-- statement:
--   The P2 M Formalism Basic Notions Examples  places Of conj val 2dcd27a70c74 construction uses the P2 M Formalism Basic Notions Examples  places Of conj val 2dcd27a70c74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L329-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L329-L331

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
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_BasicNotions_Examples__placesOf_conj_val_2dcd27a70c74 (w : (placesOf K).Pl) (x : K) :
    (placesOf K).val ((placesOf K).conj w) x = (placesOf K).val w (star x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«placesOf_conj_val» := P2M_Formalism_BasicNotions_Examples__placesOf_conj_val_2dcd27a70c74
