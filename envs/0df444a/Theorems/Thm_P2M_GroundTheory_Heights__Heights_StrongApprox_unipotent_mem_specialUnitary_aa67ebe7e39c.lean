-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:42.217195+00:00
-- url     : https://prove2.me/theorems/75fef0e1-a156-418e-8b53-4df1bcc9601e
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx unipotent mem special Unitary aa67ebe7e39c: P2 M Ground Theory Heights  Heights Strong Approx unipotent mem special Unitary aa67ebe7e39c
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx unipotent mem special Unitary aa67ebe7e39c construction uses the P2 M Ground Theory Heights  Heights Strong Approx unipotent mem special Unitary aa67ebe7e39c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L414-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L414-L416

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c : g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«unipotent_mem_specialUnitary» := P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_specialUnitary_aa67ebe7e39c
