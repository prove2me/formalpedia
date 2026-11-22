-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a
-- name    : P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:03.119806+00:00
-- url     : https://prove2.me/theorems/079a4484-bfc6-4c9b-993e-c9e4f58ebfdc
-- title:
--   P2 M Formalism Basic Notions Examples  Level Valuation Rings hida Setting Of Even 6fc5b055357a: P2 M Formalism Basic Notions Examples  Level Valuation Rings hida Setting Of Even 6fc5b055357a
-- statement:
--   The P2 M Formalism Basic Notions Examples  Level Valuation Rings hida Setting Of Even 6fc5b055357a construction uses the P2 M Formalism Basic Notions Examples  Level Valuation Rings hida Setting Of Even 6fc5b055357a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L59-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L59-L86

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (Wn p n) (Qn p n) (On p n) (Kn p n) (iotaN p n) (sigN p n)
      (algebraMap (Wn p n) (On p n)) ω := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LevelValuationRings».«hidaSettingOfEven» := P2M_Formalism_BasicNotions_Examples__LevelValuationRings_hidaSettingOfEven_6fc5b055357a
