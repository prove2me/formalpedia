-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_invol_0285d3393774
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_invol_0285d3393774
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:52.149802+00:00
-- url     : https://prove2.me/theorems/dd44f5b0-36c3-46c7-950d-fe8a327887b1
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx sig V invol 0285d3393774: P2 M Ground Theory Heights  Heights Strong Approx sig V invol 0285d3393774
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx sig V invol 0285d3393774 construction uses the P2 M Ground Theory Heights  Heights Strong Approx sig V invol 0285d3393774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L337-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L337-L342

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_invol_0285d3393774 (v : HeightOneSpectrum (𝓞 ℚ)) (x : Kv GaussQ v) :
    sigV (conj ℚ GaussQ) v (sigV (conj ℚ GaussQ) v x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«sigV_invol» := P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_invol_0285d3393774
