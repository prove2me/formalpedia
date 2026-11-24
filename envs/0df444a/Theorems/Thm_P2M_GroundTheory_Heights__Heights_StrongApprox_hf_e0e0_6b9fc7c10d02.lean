-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:26.598216+00:00
-- url     : https://prove2.me/theorems/e61faf24-8ed2-43cc-9daf-afcfbd010901
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx hf e0e0 6b9fc7c10d02: P2 M Ground Theory Heights  Heights Strong Approx hf e0e0 6b9fc7c10d02
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx hf e0e0 6b9fc7c10d02 construction uses the P2 M Ground Theory Heights  Heights Strong Approx hf e0e0 6b9fc7c10d02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L317-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L317-L318

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02 : hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«hf_e0e0» := P2M_GroundTheory_Heights__Heights_StrongApprox_hf_e0e0_6b9fc7c10d02
