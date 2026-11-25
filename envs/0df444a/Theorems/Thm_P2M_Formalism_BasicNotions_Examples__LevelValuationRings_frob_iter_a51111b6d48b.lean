-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b
-- name    : P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:02.350219+00:00
-- url     : https://prove2.me/theorems/10db62a6-dd2d-4b48-9eab-8fd8a51f2a5d
-- title:
--   P2 M Formalism Basic Notions Examples  Level Valuation Rings frob iter a51111b6d48b: P2 M Formalism Basic Notions Examples  Level Valuation Rings frob iter a51111b6d48b
-- statement:
--   The P2 M Formalism Basic Notions Examples  Level Valuation Rings frob iter a51111b6d48b construction uses the P2 M Formalism Basic Notions Examples  Level Valuation Rings frob iter a51111b6d48b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L35-L40

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

theorem P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b (hn : n ≠ 0) (x : Wn p n) : (WittVector.frobenius^[n]) x = x := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LevelValuationRings».«frob_iter» := P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b
