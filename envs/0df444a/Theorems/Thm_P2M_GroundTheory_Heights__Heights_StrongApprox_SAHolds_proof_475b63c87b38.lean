-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_proof_475b63c87b38
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_proof_475b63c87b38
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:59.256805+00:00
-- url     : https://prove2.me/theorems/7d3972db-ab2e-48a1-a596-d88aa732eb1f
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx SAHolds proof 475b63c87b38: P2 M Ground Theory Heights  Heights Strong Approx SAHolds proof 475b63c87b38
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx SAHolds proof 475b63c87b38 construction uses the P2 M Ground Theory Heights  Heights Strong Approx SAHolds proof 475b63c87b38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAHolds.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PSAHolds.lean#L57-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAHolds
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_proof_475b63c87b38 (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«SAHolds».«proof» := P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_proof_475b63c87b38
