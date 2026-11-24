-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:21.035384+00:00
-- url     : https://prove2.me/theorems/fd852dfb-9e75-4d8a-9e9b-147d268c6e8a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists mul eq zero of mem associated Prime 661bba168f30: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists mul eq zero of mem associated Prime 661bba168f30 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists mul eq zero of mem associated Prime 661bba168f30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L58-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L58-L85

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30 {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hR : SerreR B 1) (hS : SerreS B 2) {Q : Ideal B} (hQ : IsAssociatedPrime Q B) {q : B} (hq : q ∈ Q) :
    ∃ t ∉ Q, t * q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_mul_eq_zero_of_mem_associatedPrime» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_mul_eq_zero_of_mem_associatedPrime_661bba168f30
