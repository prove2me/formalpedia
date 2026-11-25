-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:41.837963+00:00
-- url     : https://prove2.me/theorems/38696bdf-4206-4f26-9e11-e4cec8fc1954
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim le one of colon span c4b38d3fa296: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim le one of colon span c4b38d3fa296 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ring Krull Dim le one of colon span c4b38d3fa296 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L87-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L87-L124

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296 {B : Type*} [CommRing B] [IsNoetherianRing B] (hS : SerreS B 2)
    {b y : B} (hb : b ∈ nonZeroDivisors B) (Q : Ideal B) [Q.IsPrime]
    (hQ : ∀ r, r ∈ Q ↔ r * y ∈ Ideal.span {b}) : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ringKrullDim_le_one_of_colon_span» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_le_one_of_colon_span_c4b38d3fa296
