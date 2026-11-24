-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:29.195316+00:00
-- url     : https://prove2.me/theorems/226b5329-2bce-48b0-af78-42b8c45c33c8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weakly Regular eq nil of socle 6d4a27b52f7e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weakly Regular eq nil of socle 6d4a27b52f7e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weakly Regular eq nil of socle 6d4a27b52f7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/ExistsMulEqZeroOfMemAssociatedPrime.lean#L12-L20

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {z : M} (hz : z ≠ 0) (hk : ∀ r ∈ maximalIdeal R, r • z = 0) {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsWeaklyRegular M rs) : rs = [] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weaklyRegular_eq_nil_of_socle» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e
