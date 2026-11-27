-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_Cl_f768e6f2d41f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_Cl_f768e6f2d41f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:47.404624+00:00
-- url     : https://prove2.me/theorems/5f45cb67-fbf1-4aa0-b618-e050fd40afa0
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx one mem Cl f768e6f2d41f: P2 M Ground Theory Heights  Heights Strong Approx one mem Cl f768e6f2d41f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx one mem Cl f768e6f2d41f construction uses the P2 M Ground Theory Heights  Heights Strong Approx one mem Cl f768e6f2d41f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L386-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L386-L387

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_Cl_f768e6f2d41f : (1 : Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ)) ∈ Cl (conj ℚ GaussQ) hypPlane := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«one_mem_Cl» := P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_Cl_f768e6f2d41f
