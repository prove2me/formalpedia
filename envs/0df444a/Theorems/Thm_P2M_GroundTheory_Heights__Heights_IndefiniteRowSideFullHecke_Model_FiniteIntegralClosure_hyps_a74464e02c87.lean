-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_hyps_a74464e02c87
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_hyps_a74464e02c87
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:30.410363+00:00
-- url     : https://prove2.me/theorems/7429104e-befd-5a8e-8cac-95a9d1c24ab1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure hyps a74464e02c87: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Inte
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure hyps a74464e02c87 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Finite Integral Closure hyps a74464e02c87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L511-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L511-L518

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_hyps_a74464e02c87 :
    (Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ) ∧
    (IsIntegral specInt ∧ IsFiniteTypeOverZ specInt ∧
      FiniteDimensional specInt.functionField specInt.functionField ∧
      IsAffineOpen (⊤ : specInt.Opens) ∧ Nonempty (⊤ : specInt.Opens)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«FiniteIntegralClosure».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_hyps_a74464e02c87
