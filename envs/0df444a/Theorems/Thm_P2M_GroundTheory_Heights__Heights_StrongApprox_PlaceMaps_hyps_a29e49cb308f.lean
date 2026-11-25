-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_hyps_a29e49cb308f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_hyps_a29e49cb308f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:58.867806+00:00
-- url     : https://prove2.me/theorems/7d1f451e-b980-5bd7-94c5-a7e381b6ec90
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps hyps a29e49cb308f: P2 M Ground Theory Heights  Heights Strong Approx Place Maps hyps a29e49cb308f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps hyps a29e49cb308f construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps hyps a29e49cb308f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L490-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L490-L494

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
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
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_hyps_a29e49cb308f :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ v3 ≠ v5 ∧
      g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_hyps_a29e49cb308f
