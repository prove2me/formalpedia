-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_proof_837219d902a0
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_proof_837219d902a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:55.600571+00:00
-- url     : https://prove2.me/theorems/26f93f52-f0f2-4cc2-b065-185379897a7f
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Local In Closure proof 837219d902a0: P2 M Ground Theory Heights  Heights Strong Approx Local In Closure proof 837219d902a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Local In Closure proof 837219d902a0 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Local In Closure proof 837219d902a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PLocalInClosure.lean#L11-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PLocalInClosure.lean#L11-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PLocalInClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_proof_837219d902a0 (hHP : HypPairExists.Statement) (hCl : ClosureIsSubmonoid.Statement)
    (hLR : LocalRingHypotheses.Statement) (hPM : PlaceMaps.Statement)
    (hEA : EichlerAtPlace.Statement) : LocalInClosure.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«LocalInClosure».«proof» := P2M_GroundTheory_Heights__Heights_StrongApprox_LocalInClosure_proof_837219d902a0
