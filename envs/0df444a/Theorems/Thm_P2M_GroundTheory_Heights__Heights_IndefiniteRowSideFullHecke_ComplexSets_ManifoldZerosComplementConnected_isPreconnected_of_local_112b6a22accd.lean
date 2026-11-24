-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:07.069313+00:00
-- url     : https://prove2.me/theorems/5f920c13-1009-44a9-8d41-97edb0bf4524
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected of local 112b6a22accd: P2 M Ground Theory Heights  Heights Indefinit
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected of local 112b6a22accd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Manifold Zeros Complement Connected is Preconnected of local 112b6a22accd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PManifoldZerosComplementConnected.lean#L9-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
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
open Topology Filter Set

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ManifoldZerosComplementConnected».«isPreconnected_of_local» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
