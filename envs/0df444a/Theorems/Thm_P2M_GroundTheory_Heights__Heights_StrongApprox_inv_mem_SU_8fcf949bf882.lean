-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:11.344881+00:00
-- url     : https://prove2.me/theorems/d7998540-a89d-41e9-a186-73cb4c8ef38b
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx inv mem SU 8fcf949bf882: P2 M Ground Theory Heights  Heights Strong Approx inv mem SU 8fcf949bf882
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx inv mem SU 8fcf949bf882 construction uses the P2 M Ground Theory Heights  Heights Strong Approx inv mem SU 8fcf949bf882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L432-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L432-L442

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882 {R : Type*} [CommRing R] (σ : R →+* R) {N : ℕ} (J : Matrix (Fin N) (Fin N) R)
    {a : Matrix (Fin N) (Fin N) R} (ha : a ∈ SU σ J) : a⁻¹ ∈ SU σ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«inv_mem_SU» := P2M_GroundTheory_Heights__Heights_StrongApprox_inv_mem_SU_8fcf949bf882
