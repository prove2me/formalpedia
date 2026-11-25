-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_analyticAt_827979e2ede3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_analyticAt_827979e2ede3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:17.286908+00:00
-- url     : https://prove2.me/theorems/afcb23e1-ff87-45c9-9b0c-5790141fbfc2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre Esymm analytic At 827979e2ede3: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre Esymm analytic At 827979e2ede3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Proper Sheeted Fibre Esymm fibre Esymm analytic At 827979e2ede3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperSheetedFibreEsymm.lean#L106-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProperSheetedFibreEsymm.lean#L106-L121

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_analyticAt_827979e2ede3 {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ)
    (hD : IsOpen D) (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) : AnalyticAt ℂ (fibreEsymm Y A l j) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ProperSheetedFibreEsymm».«fibreEsymm_analyticAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_fibreEsymm_analyticAt_827979e2ede3
