-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20
-- name    : P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:21.852729+00:00
-- url     : https://prove2.me/theorems/fe78bbcc-225e-4372-a5dd-89addd33a468
-- title:
--   P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N period ae7893d3da20: P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N period ae7893d3da20
-- statement:
--   The P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N period ae7893d3da20 construction uses the P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N period ae7893d3da20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L52-L57

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

theorem P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20 (hn : n ≠ 0) : sigN p n ^ n = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LevelValuationRings».«sigN_period» := P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_period_ae7893d3da20
