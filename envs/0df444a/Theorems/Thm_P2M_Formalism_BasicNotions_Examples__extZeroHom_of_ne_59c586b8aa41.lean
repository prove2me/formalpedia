-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41
-- name    : P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:20.424872+00:00
-- url     : https://prove2.me/theorems/65e0af97-2db0-43e8-9155-c6538065cb7e
-- title:
--   P2 M Formalism Basic Notions Examples  ext Zero Hom of ne 59c586b8aa41: P2 M Formalism Basic Notions Examples  ext Zero Hom of ne 59c586b8aa41
-- statement:
--   The P2 M Formalism Basic Notions Examples  ext Zero Hom of ne 59c586b8aa41 construction uses the P2 M Formalism Basic Notions Examples  ext Zero Hom of ne 59c586b8aa41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L106-L108

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_UnitsPowSurjective
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
open Cardinal

theorem P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41 {K L : Type*} [Field K] [Field L] (χ : Kˣ →* Lˣ) {x : K} (h : x ≠ 0) :
    extZeroHom χ x = (χ (Units.mk0 x h) : L) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«extZeroHom_of_ne» := P2M_Formalism_BasicNotions_Examples__extZeroHom_of_ne_59c586b8aa41
