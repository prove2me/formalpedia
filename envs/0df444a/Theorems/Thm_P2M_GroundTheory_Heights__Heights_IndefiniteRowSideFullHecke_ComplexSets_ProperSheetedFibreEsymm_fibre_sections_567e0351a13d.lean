-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibre_sections_567e0351a13d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibre_sections_567e0351a13d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:32.754557+00:00
-- url     : https://prove2.me/theorems/fd3f0e8d-4162-4b3f-b5da-ae57e8652370
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre sections 567e0351a13d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hec
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre sections 567e0351a13d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre sections 567e0351a13d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperSheetedFibreEsymm.lean#L29-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperSheetedFibreEsymm.lean#L29-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm
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
open Topology Filter Set Complex
open scoped Real
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibre_sections_567e0351a13d {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) :
    ∃ (F : Finset (σ → ℂ)) (g : (σ → ℂ) → (Fin d → ℂ) → σ → ℂ), (∀ x ∈ F, AnalyticAt ℂ (g x) y) ∧
      ∀ᶠ y' in 𝓝 y, Set.InjOn (fun x => g x y') ↑F ∧
        {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' ↑F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ProperSheetedFibreEsymm».«fibre_sections» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibre_sections_567e0351a13d
