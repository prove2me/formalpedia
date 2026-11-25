-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerAlong_c441d5fa2cf2
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerAlong_c441d5fa2cf2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:20.388803+00:00
-- url     : https://prove2.me/theorems/6e950365-9c41-451b-aa5d-38cae64bca6f
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Along c441d5fa2cf2: P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Along c441d5fa2cf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Along c441d5fa2cf2 construction uses the P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Along c441d5fa2cf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L398-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L398-L404

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerAlong_c441d5fa2cf2 :
    g5 ∈ eichAlong (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
      (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«unipotent_mem_eichlerAlong» := P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerAlong_c441d5fa2cf2
