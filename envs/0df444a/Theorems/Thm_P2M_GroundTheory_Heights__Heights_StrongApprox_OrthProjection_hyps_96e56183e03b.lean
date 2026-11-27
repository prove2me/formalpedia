-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_OrthProjection_hyps_96e56183e03b
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_OrthProjection_hyps_96e56183e03b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:15.412886+00:00
-- url     : https://prove2.me/theorems/821d0e41-ecdc-5d51-92ff-b0cd86025d3f
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Orth Projection hyps 96e56183e03b: P2 M Ground Theory Heights  Heights Strong Approx Orth Projection hyps 96e56183e03b
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Orth Projection hyps 96e56183e03b construction uses the P2 M Ground Theory Heights  Heights Strong Approx Orth Projection hyps 96e56183e03b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L460-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L460-L468

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_OrthProjection_hyps_96e56183e03b :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«OrthProjection».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_OrthProjection_hyps_96e56183e03b
