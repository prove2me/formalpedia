-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79
-- name    : P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:28.939362+00:00
-- url     : https://prove2.me/theorems/9e3733fe-ba8b-4216-8b3d-135bdabe6289
-- title:
--   P2 M Ground Theory Heights  Heights Model Finite Integral Closure hypotheses inhabited 1deaa4585a79: P2 M Ground Theory Heights  Heights Model Finite Integral Closure hypotheses inhabited 1deaa4585a79
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Finite Integral Closure hypotheses inhabited 1deaa4585a79 construction uses the P2 M Ground Theory Heights  Heights Model Finite Integral Closure hypotheses inhabited 1deaa4585a79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L641-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L641-L644

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79 :
    IsDomain ℤ ∧ Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧
      FiniteDimensional ℚ (CyclotomicField 3 ℚ) ∧ IsScalarTower ℤ ℚ (CyclotomicField 3 ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FiniteIntegralClosure».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79
