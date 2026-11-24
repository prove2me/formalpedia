-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_LiftingTheory_volCrude
-- name    : UpperTheory.Reformulated.B.LiftingTheory.volCrude
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:40.790798+00:00
-- url     : https://prove2.me/theorems/825b9d12-352a-421e-a783-fc9d76678089
-- title:
--   Lifting Theory: vol Crude
-- statement:
--   The Lifting Theory construction uses the vol Crude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LiftingTheory.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LiftingTheory.lean#L47-L61

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapMulVolumeOfSubgroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.LiftingTheory.volCrude :
    Formalism.FourierDecayAlt.B2.VolCrude := by sorry
