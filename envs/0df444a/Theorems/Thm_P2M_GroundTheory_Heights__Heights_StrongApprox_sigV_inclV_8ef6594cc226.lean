-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:01.363397+00:00
-- url     : https://prove2.me/theorems/2dd211ac-ff75-424a-a354-8b432911539a
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx sig V incl V 8ef6594cc226: P2 M Ground Theory Heights  Heights Strong Approx sig V incl V 8ef6594cc226
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx sig V incl V 8ef6594cc226 construction uses the P2 M Ground Theory Heights  Heights Strong Approx sig V incl V 8ef6594cc226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L350-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L350-L352

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226 (v : HeightOneSpectrum (𝓞 ℚ)) (x : GaussQ) :
    sigV (conj ℚ GaussQ) v (inclV GaussQ v x) = inclV GaussQ v (conj ℚ GaussQ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«sigV_inclV» := P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226
