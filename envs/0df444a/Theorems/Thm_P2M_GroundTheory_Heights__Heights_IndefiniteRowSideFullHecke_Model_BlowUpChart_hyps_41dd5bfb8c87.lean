-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_hyps_41dd5bfb8c87
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_hyps_41dd5bfb8c87
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:07.84835+00:00
-- url     : https://prove2.me/theorems/27185756-8af6-5138-b588-289a25f3e1f7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart hyps 41dd5bfb8c87: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart hyps 41
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart hyps 41dd5bfb8c87 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart hyps 41dd5bfb8c87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L442-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L442-L448

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_hyps_41dd5bfb8c87 :
    IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
    ∃ i, ![(2 : ℤ_[2])] i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«BlowUpChart».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_hyps_41dd5bfb8c87
