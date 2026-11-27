-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_ClosureIsSubmonoid_hyps_173fb0052cdd
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_ClosureIsSubmonoid_hyps_173fb0052cdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:40.368789+00:00
-- url     : https://prove2.me/theorems/7549c1a4-c3a7-4bc3-b7f9-dff97972cf07
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Closure Is Submonoid hyps 173fb0052cdd: P2 M Ground Theory Heights  Heights Strong Approx Closure Is Submonoid hyps 173fb0052cdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Closure Is Submonoid hyps 173fb0052cdd construction uses the P2 M Ground Theory Heights  Heights Strong Approx Closure Is Submonoid hyps 173fb0052cdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L477-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L477-L484

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_ClosureIsSubmonoid_hyps_173fb0052cdd :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«ClosureIsSubmonoid».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_ClosureIsSubmonoid_hyps_173fb0052cdd
