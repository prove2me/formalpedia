-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_proof_1d4d9dd6b940
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_proof_1d4d9dd6b940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:05.453357+00:00
-- url     : https://prove2.me/theorems/5c9c1339-2bb4-4143-b423-97736fb97048
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds proof 1d4d9dd6b940: P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds proof 1d4d9dd6b940
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds proof 1d4d9dd6b940 construction uses the P2 M Ground Theory Heights  Heights Strong Approx SAOpen Holds proof 1d4d9dd6b940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAOpenHolds.lean#L26-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAOpenHolds.lean#L26-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAOpenHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_proof_1d4d9dd6b940 (hSA : SAHolds.Statement) (hTop : AETopologicalRing.Statement) :
    SAOpenHolds.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«SAOpenHolds».«proof» := P2M_GroundTheory_Heights__Heights_StrongApprox_SAOpenHolds_proof_1d4d9dd6b940
