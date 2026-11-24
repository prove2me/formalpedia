-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_proof_a0b2351b3136
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_proof_a0b2351b3136
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:31.001799+00:00
-- url     : https://prove2.me/theorems/4f4bb899-ed5d-403c-85a3-667ef9eb9731
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods proof a0b2351b3136: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods proof a0b2351b3136
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods proof a0b2351b3136 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods proof a0b2351b3136 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L172-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
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
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_proof_a0b2351b3136 (_hT : AETopologicalRing.Statement) (hP : PlaceMaps.Statement) :
    AENeighbourhoods.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«proof» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_proof_a0b2351b3136
