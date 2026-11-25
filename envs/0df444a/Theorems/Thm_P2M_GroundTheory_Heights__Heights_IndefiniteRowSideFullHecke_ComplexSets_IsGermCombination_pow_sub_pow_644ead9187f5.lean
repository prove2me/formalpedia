-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_pow_sub_pow_644ead9187f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_pow_sub_pow_644ead9187f5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:38.822009+00:00
-- url     : https://prove2.me/theorems/c444115b-ac50-48fa-8580-fe2c5d973003
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination pow sub pow 644ead9187f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination pow sub pow 644ead9187f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination pow sub pow 644ead9187f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L61-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_pow_sub_pow_644ead9187f5 {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (h : IsGermCombination w p (fun z => f z - g z)) (n : ℕ) :
    IsGermCombination w p (fun z => f z ^ n - g z ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«IsGermCombination».«pow_sub_pow» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_pow_sub_pow_644ead9187f5
