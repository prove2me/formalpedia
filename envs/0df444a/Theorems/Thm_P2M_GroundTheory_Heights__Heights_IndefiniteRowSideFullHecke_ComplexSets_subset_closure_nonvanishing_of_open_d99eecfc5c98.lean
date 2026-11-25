-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_subset_closure_nonvanishing_of_open_d99eecfc5c98
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_subset_closure_nonvanishing_of_open_d99eecfc5c98
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:08.650796+00:00
-- url     : https://prove2.me/theorems/894972e6-d495-4756-87e9-4c515eeac951
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets subset closure nonvanishing of open d99eecfc5c98: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets subset closure nonvanishing of open d99eecfc5c98 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets subset closure nonvanishing of open d99eecfc5c98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperOpenProjectionCover.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperOpenProjectionCover.lean#L11-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionBranchLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionCover
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
open Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_subset_closure_nonvanishing_of_open_d99eecfc5c98 {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«subset_closure_nonvanishing_of_open» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_subset_closure_nonvanishing_of_open_d99eecfc5c98
