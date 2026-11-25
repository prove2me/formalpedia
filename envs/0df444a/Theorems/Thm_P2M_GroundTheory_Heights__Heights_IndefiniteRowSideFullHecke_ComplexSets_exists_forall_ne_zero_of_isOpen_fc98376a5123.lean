-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:53.303957+00:00
-- url     : https://prove2.me/theorems/9286ac1f-c0f0-401c-b738-273bfa7b0ae9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists forall ne zero of is Open fc98376a5123: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comple
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists forall ne zero of is Open fc98376a5123 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists forall ne zero of is Open fc98376a5123 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperOpenProjectionLocalUnbranched.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperOpenProjectionLocalUnbranched.lean#L11-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionLocalUnbranched
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
open Topology Metric Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123 {E ι : Type} [TopologicalSpace E] (s : Finset ι)
    (G : ι → E → ℂ) (U : Set E) (hc : ∀ i ∈ s, ContinuousOn (G i) U)
    (hne : ∀ i ∈ s, ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, G i t ≠ 0) :
    ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, ∀ i ∈ s, G i t ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_forall_ne_zero_of_isOpen» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123
