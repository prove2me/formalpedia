-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:28.02247+00:00
-- url     : https://prove2.me/theorems/eff23d20-22b7-4b26-ac9b-b2fa7f6eb4f9
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm  a969c2c0434a: P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm  a969c2c0434a
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm  a969c2c0434a construction uses the P2 M Ground Theory Heights  Heights Strong Approx hyp Plane herm  a969c2c0434a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L309-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L309-L309

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a : hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«hypPlane_herm'» := P2M_GroundTheory_Heights__Heights_StrongApprox_hypPlane_herm__a969c2c0434a
