-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:31.79053+00:00
-- url     : https://prove2.me/theorems/b552f333-7474-4e35-8df7-0edbb1800da9
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx gauss invol b290ae2f2fc0: P2 M Ground Theory Heights  Heights Strong Approx gauss invol b290ae2f2fc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx gauss invol b290ae2f2fc0 construction uses the P2 M Ground Theory Heights  Heights Strong Approx gauss invol b290ae2f2fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L295-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L295-L296

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0 (x : GaussQ) : (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«gauss_invol» := P2M_GroundTheory_Heights__Heights_StrongApprox_gauss_invol_b290ae2f2fc0
