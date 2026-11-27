-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hyps_abfc8ab07388
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hyps_abfc8ab07388
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:59.062809+00:00
-- url     : https://prove2.me/theorems/21192c1b-d1cd-42b9-b3f0-bc10917cf3d7
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hyps abfc8ab07388: P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hyps abfc8ab07388
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hyps abfc8ab07388 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Eichler At Place hyps abfc8ab07388 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L496-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L496-L502

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hyps_abfc8ab07388 :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      g5 ∈ eichSet (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
        (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EichlerAtPlace».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hyps_abfc8ab07388
