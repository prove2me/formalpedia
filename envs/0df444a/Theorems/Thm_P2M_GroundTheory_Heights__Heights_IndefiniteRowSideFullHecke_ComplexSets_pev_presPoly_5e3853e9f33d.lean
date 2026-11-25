-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:08.130847+00:00
-- url     : https://prove2.me/theorems/d630503d-370e-48a9-8627-9f09aab62dfb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev pres Poly 5e3853e9f33d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev pres Pol
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev pres Poly 5e3853e9f33d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev pres Poly 5e3853e9f33d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L145-L148

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) (y : Fin d → ℂ) (t : ℂ) :
    pev y t (presPoly c hc) = t ^ N + ∑ j, c j y * t ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«pev_presPoly» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d
