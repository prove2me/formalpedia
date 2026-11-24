-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:11.243521+00:00
-- url     : https://prove2.me/theorems/39063724-db26-41f3-ad84-20390ef57e98
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mul algebra Map mem map of le colon 7284726482a3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mul algebra Map mem map of le colon 7284726482a3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mul algebra Map mem map of le colon 7284726482a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L35-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3 {B : Type*} [CommRing B] (Q : Ideal B) [Q.IsPrime] (I : Ideal B)
    {y : B} (hy : ∀ r ∈ Q, r * y ∈ I) :
    ∀ m ∈ maximalIdeal (Localization.AtPrime Q),
      m * algebraMap B (Localization.AtPrime Q) y ∈ I.map (algebraMap B (Localization.AtPrime Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mul_algebraMap_mem_map_of_le_colon» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mul_algebraMap_mem_map_of_le_colon_7284726482a3
