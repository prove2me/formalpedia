-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:29.422916+00:00
-- url     : https://prove2.me/theorems/05270d87-932d-4267-9b76-ccdffe3bcf9f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sq Zero Frobenius Lift mk 9f7e8c1b72b5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sq Zero Frobenius Lift mk 9f7e8c1b72b5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets sq Zero Frobenius Lift mk 9f7e8c1b72b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothFrobeniusLift.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothFrobeniusLift.lean#L46-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
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
variable {C : Type*} [CommRing C] {N : Ideal C} {p : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5 (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) :
    sqZeroFrobeniusLift N hp hpC hN (Ideal.Quotient.mk N c) = c ^ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«sqZeroFrobeniusLift_mk» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sqZeroFrobeniusLift_mk_9f7e8c1b72b5
