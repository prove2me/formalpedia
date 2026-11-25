-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_cons_tailL_bc1d6b87226f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_cons_tailL_bc1d6b87226f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:26.022904+00:00
-- url     : https://prove2.me/theorems/94c68fb7-dc08-4eab-86d5-20ccf1a8f09a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic cons tail L bc1d6b87226f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Heck
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic cons tail L bc1d6b87226f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Sheet Piece Product Analytic cons tail L bc1d6b87226f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetPieceProductAnalytic.lean#L24-L26

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_cons_tailL_bc1d6b87226f {d : ℕ} (p : Fin (d + 1) → ℂ) : (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«SheetPieceProductAnalytic».«cons_tailL» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_cons_tailL_bc1d6b87226f
