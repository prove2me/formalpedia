-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_perpProjection_isotropic_self_ee74c94830c0
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_perpProjection_isotropic_self_ee74c94830c0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:10.012164+00:00
-- url     : https://prove2.me/theorems/cf443067-3fcf-55cf-a6d2-9c23e7638733
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx perp Projection isotropic self ee74c94830c0: P2 M Ground Theory Heights  Heights Strong Approx perp Projection isotropic self ee74c94830c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx perp Projection isotropic self ee74c94830c0 construction uses the P2 M Ground Theory Heights  Heights Strong Approx perp Projection isotropic self ee74c94830c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L389-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L389-L392

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_perpProjection_isotropic_self_ee74c94830c0 : perpProj (conj ℚ GaussQ).toRingHom hypPlane e0 f0 e0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«perpProjection_isotropic_self» := P2M_GroundTheory_Heights__Heights_StrongApprox_perpProjection_isotropic_self_ee74c94830c0
