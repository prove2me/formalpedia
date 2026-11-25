-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:29.126543+00:00
-- url     : https://prove2.me/theorems/a165cdb9-edb7-4a48-a8f2-e77efe2659b5
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx hyperbolic Plane hermitian at five 95fc9fec3fa8: P2 M Ground Theory Heights  Heights Strong Approx hyperbolic Plane hermitian at five 95fc9fec3fa8
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx hyperbolic Plane hermitian at five 95fc9fec3fa8 construction uses the P2 M Ground Theory Heights  Heights Strong Approx hyperbolic Plane hermitian at five 95fc9fec3fa8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L410-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L410-L412

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8 : (hypPlane.map (inclV GaussQ v5))ᵀ =
    (hypPlane.map (inclV GaussQ v5)).map (sigV (conj ℚ GaussQ) v5).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«hyperbolicPlane_hermitian_at_five» := P2M_GroundTheory_Heights__Heights_StrongApprox_hyperbolicPlane_hermitian_at_five_95fc9fec3fa8
