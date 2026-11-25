-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629
-- name    : P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:01.585455+00:00
-- url     : https://prove2.me/theorems/47f8e448-896a-427c-a454-95cb63915b5c
-- title:
--   P2 M Formalism Basic Notions Examples  det Ideal ne bot ac7c91201629: P2 M Formalism Basic Notions Examples  det Ideal ne bot ac7c91201629
-- statement:
--   The P2 M Formalism Basic Notions Examples  det Ideal ne bot ac7c91201629 construction uses the P2 M Formalism Basic Notions Examples  det Ideal ne bot ac7c91201629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L39-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L39-L61

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

theorem P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629 (L : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) : detIdeal L ≠ ⊥ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«detIdeal_ne_bot» := P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629
