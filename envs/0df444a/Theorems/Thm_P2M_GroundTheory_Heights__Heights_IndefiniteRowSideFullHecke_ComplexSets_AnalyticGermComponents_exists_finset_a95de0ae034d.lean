-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_exists_finset_a95de0ae034d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_exists_finset_a95de0ae034d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:06.277557+00:00
-- url     : https://prove2.me/theorems/979d0fc5-482a-4c04-8516-6fa124b1feab
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components exists finset a95de0ae034d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components exists finset a95de0ae034d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components exists finset a95de0ae034d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L90-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L90-L148

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_exists_finset_a95de0ae034d {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«AnalyticGermComponents».«exists_finset» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_exists_finset_a95de0ae034d
