-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:33.477107+00:00
-- url     : https://prove2.me/theorems/28e5b336-9b21-4a13-8018-8ac63c3dc6c0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic differentiable At prod Fn c88dec3fd0bb: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic differentiable At prod Fn c88dec3fd0bb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic differentiable At prod Fn c88dec3fd0bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L56-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L56-L137

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«SheetPieceProductAnalytic».«differentiableAt_prodFn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb
