-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:25.268751+00:00
-- url     : https://prove2.me/theorems/31993032-d8a7-5df4-b5e0-3c52b173bb10
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic is Bounded prod Fn db45f8a99bed: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic is Bounded prod Fn db45f8a99bed construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic is Bounded prod Fn db45f8a99bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L139-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L139-L183

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedFibreSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetPieceProductAnalytic
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
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«SheetPieceProductAnalytic».«isBounded_prodFn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed
