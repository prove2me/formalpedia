-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_of_germ_eq_b6b3c7fcfce8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_of_germ_eq_b6b3c7fcfce8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:06.003088+00:00
-- url     : https://prove2.me/theorems/297bfc5d-ad0f-4db1-8e8c-01e1c4c21f38
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually of germ eq b6b3c7fcfce8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets even
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually of germ eq b6b3c7fcfce8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually of germ eq b6b3c7fcfce8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPrimitiveForm.lean#L163-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_of_germ_eq_b6b3c7fcfce8 {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eventually_of_germ_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_of_germ_eq_b6b3c7fcfce8
