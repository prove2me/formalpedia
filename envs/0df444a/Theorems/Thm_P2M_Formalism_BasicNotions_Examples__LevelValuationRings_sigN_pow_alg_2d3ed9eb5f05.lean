-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05
-- name    : P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:53.612766+00:00
-- url     : https://prove2.me/theorems/95c822ac-0174-4f8f-a7ba-f25761e37fdf
-- title:
--   P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N pow alg 2d3ed9eb5f05: P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N pow alg 2d3ed9eb5f05
-- statement:
--   The P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N pow alg 2d3ed9eb5f05 construction uses the P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N pow alg 2d3ed9eb5f05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L42-L50

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

theorem P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05 (k : ℕ) (x : Wn p n) :
    (sigN p n ^ k) (algebraMap (Wn p n) (Qn p n) x) =
      algebraMap (Wn p n) (Qn p n) ((WittVector.frobenius^[k]) x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LevelValuationRings».«sigN_pow_alg» := P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_pow_alg_2d3ed9eb5f05
