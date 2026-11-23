-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
-- name    : P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:08.523628+00:00
-- url     : https://prove2.me/theorems/93b82521-d288-485e-a082-e486563b4656
-- title:
--   P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N alg 337981bcf272: P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N alg 337981bcf272
-- statement:
--   The P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N alg 337981bcf272 construction uses the P2 M Formalism Basic Notions Examples  Level Valuation Rings sig N alg 337981bcf272 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean#L26-L28

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

theorem P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272 (x : Wn p n) :
    sigN p n (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) (WittVector.frobenius x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LevelValuationRings».«sigN_alg» := P2M_Formalism_BasicNotions_Examples__LevelValuationRings_sigN_alg_337981bcf272
