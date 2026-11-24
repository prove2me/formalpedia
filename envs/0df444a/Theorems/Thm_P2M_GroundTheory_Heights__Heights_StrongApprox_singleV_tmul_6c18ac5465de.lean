-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:52.59822+00:00
-- url     : https://prove2.me/theorems/173fb1fb-1e9d-433b-a6db-d62cecd36b51
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx single V tmul 6c18ac5465de: P2 M Ground Theory Heights  Heights Strong Approx single V tmul 6c18ac5465de
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx single V tmul 6c18ac5465de construction uses the P2 M Ground Theory Heights  Heights Strong Approx single V tmul 6c18ac5465de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L364-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L364-L365

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de (x : v5.adicCompletion ℚ) (y : GaussQ) :
    singleV GaussQ v5 (x ⊗ₜ[ℚ] y) = singleF ℚ v5 x ⊗ₜ[ℚ] y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«singleV_tmul» := P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de
