-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:55.296374+00:00
-- url     : https://prove2.me/theorems/aab3fba0-1933-4458-b190-4f69611d74d3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components is Analytic Near inter zero 4847adeb363d: P2 M Ground Theory Heights  Heights Indefinite Row Si
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components is Analytic Near inter zero 4847adeb363d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components is Analytic Near inter zero 4847adeb363d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L53-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L53-L71

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«AnalyticGermComponents».«isAnalyticNear_inter_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d
