-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__placesOf_ram_eq_3d0cf30d488e
-- name    : P2M_Formalism_BasicNotions_Examples__placesOf_ram_eq_3d0cf30d488e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:29.316303+00:00
-- url     : https://prove2.me/theorems/587819d4-0f8c-4075-8e6d-516e37458317
-- title:
--   P2 M Formalism Basic Notions Examples  places Of ram eq 3d0cf30d488e: P2 M Formalism Basic Notions Examples  places Of ram eq 3d0cf30d488e
-- statement:
--   The P2 M Formalism Basic Notions Examples  places Of ram eq 3d0cf30d488e construction uses the P2 M Formalism Basic Notions Examples  places Of ram eq 3d0cf30d488e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L325-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Places.lean#L325-L327

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

theorem P2M_Formalism_BasicNotions_Examples__placesOf_ram_eq_3d0cf30d488e (w : (placesOf K).Pl) :
    (placesOf K).ramIdx w = eWL K ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«placesOf_ram_eq» := P2M_Formalism_BasicNotions_Examples__placesOf_ram_eq_3d0cf30d488e
