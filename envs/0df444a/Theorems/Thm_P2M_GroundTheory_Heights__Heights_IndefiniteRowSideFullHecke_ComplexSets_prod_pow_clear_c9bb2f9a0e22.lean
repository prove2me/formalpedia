-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_pow_clear_c9bb2f9a0e22
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_pow_clear_c9bb2f9a0e22
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:31.059863+00:00
-- url     : https://prove2.me/theorems/40b4a064-520d-5e81-b020-bbd8997688d6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prod pow clear c9bb2f9a0e22: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prod pow cl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prod pow clear c9bb2f9a0e22 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prod pow clear c9bb2f9a0e22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_pow_clear_c9bb2f9a0e22 {ι : Type*} (s : Finset ι) (e : ℂ) (M : ℕ) (x : ι → ℂ) (α : ι → ℕ) :
    ∏ i ∈ s, (e ^ M * x i) ^ α i = e ^ (M * ∑ i ∈ s, α i) * ∏ i ∈ s, x i ^ α i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«prod_pow_clear» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_pow_clear_c9bb2f9a0e22
