-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EDenseInAE_hyps_290b8d7b8479
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_EDenseInAE_hyps_290b8d7b8479
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:37.102622+00:00
-- url     : https://prove2.me/theorems/39d05f59-7ea0-446c-bf15-aa814709baed
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx EDense In AE hyps 290b8d7b8479: P2 M Ground Theory Heights  Heights Strong Approx EDense In AE hyps 290b8d7b8479
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx EDense In AE hyps 290b8d7b8479 construction uses the P2 M Ground Theory Heights  Heights Strong Approx EDense In AE hyps 290b8d7b8479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L455-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L455-L458

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_EDenseInAE_hyps_290b8d7b8479 :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«EDenseInAE».«hyps» := P2M_GroundTheory_Heights__Heights_StrongApprox_EDenseInAE_hyps_290b8d7b8479
