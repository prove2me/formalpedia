-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8
-- name    : P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:20.898717+00:00
-- url     : https://prove2.me/theorems/35558398-2c23-4a08-a38d-990d65ad6b80
-- title:
--   P2 M Formalism Basic Notions Examples  iota Sub injective c0b49dbbe3d8: P2 M Formalism Basic Notions Examples  iota Sub injective c0b49dbbe3d8
-- statement:
--   The P2 M Formalism Basic Notions Examples  iota Sub injective c0b49dbbe3d8 construction uses the P2 M Formalism Basic Notions Examples  iota Sub injective c0b49dbbe3d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L199-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/UnitsPowSurjective.lean#L199-L203

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
variable (g l : ℕ) [Fact g.Prime] [Fact l.Prime]

theorem P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8 : Function.Injective (iotaSub g l) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«iotaSub_injective» := P2M_Formalism_BasicNotions_Examples__iotaSub_injective_c0b49dbbe3d8
