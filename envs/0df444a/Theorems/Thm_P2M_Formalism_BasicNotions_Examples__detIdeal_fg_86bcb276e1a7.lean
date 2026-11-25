-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7
-- name    : P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:14.139684+00:00
-- url     : https://prove2.me/theorems/ea2b1095-fa3b-4633-803a-ddf7cf55297b
-- title:
--   P2 M Formalism Basic Notions Examples  det Ideal fg 86bcb276e1a7: P2 M Formalism Basic Notions Examples  det Ideal fg 86bcb276e1a7
-- statement:
--   The P2 M Formalism Basic Notions Examples  det Ideal fg 86bcb276e1a7 construction uses the P2 M Formalism Basic Notions Examples  det Ideal fg 86bcb276e1a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L63-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L63-L107

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}

theorem P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7 (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) : (detIdeal L).FG := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«detIdeal_fg» := P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7
