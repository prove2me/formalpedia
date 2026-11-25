-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:31.478804+00:00
-- url     : https://prove2.me/theorems/3a90e7a6-72f5-449e-a587-99183d2331d5
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods of place Maps c4be2c416734: P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods of place Maps c4be2c416734
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods of place Maps c4be2c416734 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AENeighbourhoods of place Maps c4be2c416734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAENeighbourhoods.lean#L168-L170

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734 (hP : PlaceMaps.Statement) : AENeighbourhoods.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AENeighbourhoods».«of_placeMaps» := P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_of_placeMaps_c4be2c416734
