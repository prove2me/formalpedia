-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae
-- name    : P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:14.829905+00:00
-- url     : https://prove2.me/theorems/57873b6c-3523-4f49-8133-ebccbb8abd5c
-- title:
--   P2 M Formalism Basic Notions Examples  Gat R mem span om pow bf8597fdd0ae: P2 M Formalism Basic Notions Examples  Gat R mem span om pow bf8597fdd0ae
-- statement:
--   The P2 M Formalism Basic Notions Examples  Gat R mem span om pow bf8597fdd0ae construction uses the P2 M Formalism Basic Notions Examples  Gat R mem span om pow bf8597fdd0ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatRing.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatRing.lean#L107-L114

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.GatR
open QuadraticAlgebra IsLocalRing
variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}

theorem P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae (m : ℕ) (z : QuadraticAlgebra W ϖ 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} ↔ ϖ ^ m ∣ z.re ∧ ϖ ^ m ∣ z.im := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«GatR».«mem_span_om_pow» := P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae
