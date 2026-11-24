-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:00.129048+00:00
-- url     : https://prove2.me/theorems/11c17fb6-3c70-42cc-adef-50ed93bcbda8
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx hf f0f0 a1dde18274c7: P2 M Ground Theory Heights  Heights Strong Approx hf f0f0 a1dde18274c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx hf f0f0 a1dde18274c7 construction uses the P2 M Ground Theory Heights  Heights Strong Approx hf f0f0 a1dde18274c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L320-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L320-L321

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7 : hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«hf_f0f0» := P2M_GroundTheory_Heights__Heights_StrongApprox_hf_f0f0_a1dde18274c7
