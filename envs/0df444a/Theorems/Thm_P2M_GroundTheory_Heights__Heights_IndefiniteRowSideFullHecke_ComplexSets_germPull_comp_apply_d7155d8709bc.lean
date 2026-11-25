-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:09.194982+00:00
-- url     : https://prove2.me/theorems/3c451160-7f86-57d3-9936-502c18c57fe0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Pull comp apply d7155d8709bc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Pull comp apply d7155d8709bc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets germ Pull comp apply d7155d8709bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermProjectionStep.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
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
open Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc {σ τ : Type} [Fintype σ] [Fintype τ] {d : ℕ} (w : σ → ℂ)
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)) (φ : holGerms (B (π w))) :
    germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ =
      germPull π (π.analyticAt w) rfl (germPull B (B.analyticAt (π w)) rfl φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«germPull_comp_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germPull_comp_apply_d7155d8709bc
