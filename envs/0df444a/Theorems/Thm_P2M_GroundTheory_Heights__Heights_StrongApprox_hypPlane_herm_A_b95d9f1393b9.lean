-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_A_b95d9f1393b9
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_A_b95d9f1393b9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:52.712959+00:00
-- url     : https://prove2.me/theorems/dd989ad5-5692-4a3c-81c6-5f04e9b84ce7
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm A b95d9f1393b9: P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm A b95d9f1393b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm A b95d9f1393b9 construction uses the P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm A b95d9f1393b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L422-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L422-L424

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_A_b95d9f1393b9 : (hypPlane.map (inclA ℚ GaussQ))ᵀ =
    (hypPlane.map (inclA ℚ GaussQ)).map (sigA (conj ℚ GaussQ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«hypPlane_herm_A» := P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm_A_b95d9f1393b9
