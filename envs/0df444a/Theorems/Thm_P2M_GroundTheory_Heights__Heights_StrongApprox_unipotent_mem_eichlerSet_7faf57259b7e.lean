-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerSet_7faf57259b7e
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerSet_7faf57259b7e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:42.047689+00:00
-- url     : https://prove2.me/theorems/5a46a92d-87b2-4ef0-adec-486f87c51ec5
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Set 7faf57259b7e: P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Set 7faf57259b7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Set 7faf57259b7e construction uses the P2 M Ground Theory Heights  Heights Strong Approx unipotent mem eichler Set 7faf57259b7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L406-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L406-L408

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerSet_7faf57259b7e :
    g5 ∈ eichSet (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
      (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«unipotent_mem_eichlerSet» := P2M_GroundTheory_Heights__Heights_StrongApprox_unipotent_mem_eichlerSet_7faf57259b7e
